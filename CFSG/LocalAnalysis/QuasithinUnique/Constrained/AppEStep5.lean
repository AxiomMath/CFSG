module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEStep4

public section

namespace CFSG.QuasithinUnique.AppE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.DoubleA3 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {n : ℕ} {t : G}

omit [Finite G] in
theorem sq_mul_eq_commutator {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    (a * b) ^ 2 = ⁅a, b⁆ := by
  have ha' : a⁻¹ = a := inv_eq_iff_mul_eq_one.2 (by rw [← pow_two]; exact ha)
  have hb' : b⁻¹ = b := inv_eq_iff_mul_eq_one.2 (by rw [← pow_two]; exact hb)
  rw [pow_two, commutatorElement_def, ha', hb']
  simp only [mul_assoc]

omit [Finite G] in
theorem le_or_le_of_forall_mem_or {A K₁ K₂ : Subgroup G} (h : ∀ a ∈ A, a ∈ K₁ ∨ a ∈ K₂) :
    A ≤ K₁ ∨ A ≤ K₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA1, hA2⟩ := hcon
  obtain ⟨a₀, ha₀A, ha₀K⟩ := IsConcreteLE.not_le_iff_exists.mp hA1
  obtain ⟨a₁, ha₁A, ha₁K⟩ := IsConcreteLE.not_le_iff_exists.mp hA2
  have h0 : a₀ ∈ K₂ := (h a₀ ha₀A).resolve_left ha₀K
  have h1 : a₁ ∈ K₁ := (h a₁ ha₁A).resolve_right ha₁K
  rcases h (a₀ * a₁) (A.mul_mem ha₀A ha₁A) with hm | hm
  · exact ha₀K ((mul_mem_cancel_right h1).1 hm)
  · exact ha₁K ((mul_mem_cancel_left h0).1 hm)

namespace Setup

variable {M₀ : Subgroup G} {x : G} {q : ℕ} {W : Subgroup G}
  (P : Setup T M H S L n t M₀ x q W)
include P

theorem elemAb_U₁ : ElemAb2 (blockU L) := ⟨P.loc.rk.U_comm, C1.blockU_sq P.D.hL⟩

theorem elemAb_X₁ : ElemAb2 (conjSubgroup (blockU L) x) := P.elemAb_U₁.conjSubgroup x

theorem elemAb_U₂ : ElemAb2 (conjSubgroup (blockU L) t) := P.elemAb_U₁.conjSubgroup t

theorem elemAb_X₂ : ElemAb2 (conjSubgroup (conjSubgroup (blockU L) t) x) :=
  P.elemAb_U₂.conjSubgroup x

theorem a_comm_U₁ {a : G} (ha : a ∈ conjSubgroup (conjSubgroup (blockU L) t) x) :
    ∀ v ∈ blockU L, v * a = a * v := fun v hv =>
  Subgroup.mem_centralizer_iff.1 (P.U₂x_le_Q₁ ha).2 v hv

theorem x_comm_U₂ {v : G} (hv : v ∈ conjSubgroup (blockU L) x) :
    ∀ u ∈ conjSubgroup (blockU L) t, u * v = v * u := by
  have h := P.Ux_le_Q₂ hv
  rw [P.loc₂.rk.Q_eq] at h
  exact fun u hu => Subgroup.mem_centralizer_iff.1 h.2 u hu

theorem comm_mem_W₁ {x₁ u₁ : G} (hx₁ : x₁ ∈ conjSubgroup (blockU L) x) (hu₁ : u₁ ∈ blockU L) :
    ⁅x₁, u₁⁆ ∈ W := by
  have h := Subgroup.commutator_mem_commutator hu₁ hx₁
  rw [P.kf₁.commU] at h
  have := W.inv_mem h
  rwa [commutatorElement_inv] at this

theorem comm_mem_W₂ {a u₂ : G} (ha : a ∈ conjSubgroup (conjSubgroup (blockU L) t) x)
    (hu₂ : u₂ ∈ conjSubgroup (blockU L) t) : ⁅a, u₂⁆ ∈ conjSubgroup W t := by
  have h := Subgroup.commutator_mem_commutator hu₂ ha
  rw [P.kf₂.commU] at h
  have := (conjSubgroup W t).inv_mem h
  rwa [commutatorElement_inv] at this

theorem sq_B_decomp {x₁ u₁ a u₂ e f : G} (hx₁ : x₁ ∈ conjSubgroup (blockU L) x)
    (hu₁ : u₁ ∈ blockU L) (ha : a ∈ conjSubgroup (conjSubgroup (blockU L) t) x)
    (hu₂ : u₂ ∈ conjSubgroup (blockU L) t) (he : e ∈ W) (hf : f ∈ baumD S L) :
    (x₁ * (u₁ * (a * (u₂ * (e * f))))) ^ 2 = ⁅x₁, u₁⁆ * ⁅a, u₂⁆ := by
  have hWU : e ∈ blockU L := P.loc.rk.W_le_U he
  have hfD := P.D.mem_baumD_iff.1 hf
  have hfX := P.D_comm_X hf
  have c12 : Commute (x₁ * u₁) (a * u₂) := by
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
    · exact P.comm_U₁x_U₂x x₁ hx₁ a ha
    · exact (P.x_comm_U₂ hx₁ u₂ hu₂).symm
    · exact P.a_comm_U₁ ha u₁ hu₁
    · exact P.D.comm_elem u₁ (P.U₁_le_L hu₁) u₂ (P.U₂_le_L₂ hu₂)
  have c1d : Commute (x₁ * u₁) (e * f) := by
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
    · exact P.loc.rk.conj_comm x x₁ hx₁ e (P.W_le_X he)
    · exact hfX.1 x₁ hx₁
    · exact P.loc.rk.U_comm u₁ hu₁ e hWU
    · exact hfD.2.1 u₁ (P.U₁_le_L hu₁)
  have c2d : Commute (a * u₂) (e * f) := by
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
    · exact (P.a_comm_U₁ ha e hWU).symm
    · exact hfX.2 a ha
    · exact (P.D.comm_elem e (P.U₁_le_L hWU) u₂ (P.U₂_le_L₂ hu₂)).symm
    · exact hfD.2.2 u₂ (P.U₂_le_L₂ hu₂)
  have cef : Commute e f := hfD.2.1 e (P.U₁_le_L hWU)
  have hd2 : (e * f) ^ 2 = 1 := by
    rw [cef.mul_pow, P.elemAb_U₁.sq_eq_one hWU, P.D_elemAb.sq_eq_one hf, mul_one]
  have hb : x₁ * (u₁ * (a * (u₂ * (e * f)))) = (x₁ * u₁) * (a * u₂) * (e * f) := by
    simp only [mul_assoc]
  rw [hb, (c1d.mul_left c2d).mul_pow, c12.mul_pow, hd2, mul_one,
    sq_mul_eq_commutator (P.elemAb_X₁.sq_eq_one hx₁) (P.elemAb_U₁.sq_eq_one hu₁),
    sq_mul_eq_commutator (P.elemAb_X₂.sq_eq_one ha) (P.elemAb_U₂.sq_eq_one hu₂)]

theorem prod_cent {x₁ u₁ a u₂ e f : G} (hx₁ : x₁ ∈ conjSubgroup (blockU L) x)
    (hu₁ : u₁ ∈ blockU L) (ha : a ∈ conjSubgroup (conjSubgroup (blockU L) t) x)
    (hu₂ : u₂ ∈ conjSubgroup (blockU L) t) (he : e ∈ W) (hf : f ∈ baumD S L) :
    (x₁ * (u₁ * (a * (u₂ * (e * f)))) ∈ centralizer (blockU L : Set G) ↔ x₁ ∈ W) ∧
    (x₁ * (u₁ * (a * (u₂ * (e * f)))) ∈
        centralizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G) ↔ u₁ ∈ W) ∧
    (x₁ * (u₁ * (a * (u₂ * (e * f)))) ∈
        centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G) ↔
        a ∈ conjSubgroup W t) ∧
    (x₁ * (u₁ * (a * (u₂ * (e * f)))) ∈
        centralizer ((conjSubgroup (conjSubgroup (blockU L) t) x : Subgroup G) : Set G) ↔
        u₂ ∈ conjSubgroup W t) := by
  have hWU : e ∈ blockU L := P.loc.rk.W_le_U he
  have hfD := P.D.mem_baumD_iff.1 hf
  have hfX := P.D_comm_X hf
  have mc : ∀ (V : Subgroup G) (g : G), (∀ v ∈ V, v * g = g * v) →
      g ∈ centralizer (V : Set G) := fun V g h => Subgroup.mem_centralizer_iff.mpr h
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have hu₁c := mc (blockU L) u₁ fun v hv => P.loc.rk.U_comm v hv u₁ hu₁
    have hac := mc (blockU L) a (P.a_comm_U₁ ha)
    have hu₂c := mc (blockU L) u₂ fun v hv =>
      P.D.comm_elem v (P.U₁_le_L hv) u₂ (P.U₂_le_L₂ hu₂)
    have hec := mc (blockU L) e fun v hv => P.loc.rk.U_comm v hv e hWU
    have hfc := mc (blockU L) f fun v hv => hfD.2.1 v (P.U₁_le_L hv)
    have hR := (centralizer (blockU L : Set G)).mul_mem hu₁c ((centralizer (blockU L : Set G)).mul_mem
      hac ((centralizer (blockU L : Set G)).mul_mem hu₂c
        ((centralizer (blockU L : Set G)).mul_mem hec hfc)))
    rw [mul_mem_cancel_right hR]
    constructor
    · intro h
      have hB : x₁ ∈ baum S := P.kf₁.Ux_le_B hx₁
      have : x₁ ∈ conjSubgroup (blockU L) x ⊓ (baum S ⊓ centralizer (blockU L : Set G)) :=
        ⟨hx₁, hB, h⟩
      rwa [P.kf₁.infQ] at this
    · intro h
      exact mc (blockU L) x₁ fun v hv => P.loc.rk.U_comm v hv x₁ (P.loc.rk.W_le_U h)
  ·
    have hx₁c := mc (conjSubgroup (blockU L) x) x₁ fun v hv => P.loc.rk.conj_comm x v hv x₁ hx₁
    have hac := mc (conjSubgroup (blockU L) x) a fun v hv => P.comm_U₁x_U₂x v hv a ha
    have hu₂c := mc (conjSubgroup (blockU L) x) u₂ fun v hv => (P.x_comm_U₂ hv u₂ hu₂).symm
    have hec := mc (conjSubgroup (blockU L) x) e fun v hv =>
      P.loc.rk.conj_comm x v hv e (P.W_le_X he)
    have hfc := mc (conjSubgroup (blockU L) x) f fun v hv => hfX.1 v hv
    have hR := (centralizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G)).mul_mem hac
      ((centralizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G)).mul_mem hu₂c
        ((centralizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G)).mul_mem hec hfc))
    rw [mul_mem_cancel_left hx₁c, mul_mem_cancel_right hR]
    constructor
    · intro h
      have : u₁ ∈ blockU L ⊓ centralizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G) :=
        ⟨hu₁, h⟩
      rwa [P.kf₁.infC] at this
    · intro h
      exact mc (conjSubgroup (blockU L) x) u₁ fun v hv =>
        (P.loc.rk.conj_comm x u₁ (P.W_le_X h) v hv).symm
  ·
    have hx₁c := mc (conjSubgroup (blockU L) t) x₁ fun v hv => P.x_comm_U₂ hx₁ v hv
    have hu₁c := mc (conjSubgroup (blockU L) t) u₁ fun v hv =>
      (P.D.comm_elem u₁ (P.U₁_le_L hu₁) v (P.U₂_le_L₂ hv)).symm
    have hu₂c := mc (conjSubgroup (blockU L) t) u₂ fun v hv => P.loc₂.rk.U_comm v hv u₂ hu₂
    have hec := mc (conjSubgroup (blockU L) t) e fun v hv =>
      (P.D.comm_elem e (P.U₁_le_L hWU) v (P.U₂_le_L₂ hv)).symm
    have hfc := mc (conjSubgroup (blockU L) t) f fun v hv => hfD.2.2 v (P.U₂_le_L₂ hv)
    have hR := (centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G)).mul_mem hu₂c
      ((centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G)).mul_mem hec hfc)
    rw [mul_mem_cancel_left hx₁c, mul_mem_cancel_left hu₁c, mul_mem_cancel_right hR]
    constructor
    · intro h
      have haB : a ∈ baum S := P.kf₂.Ux_le_B ha
      have haQ : a ∈ conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) t := by
        rw [P.loc₂.rk.Q_eq]; exact ⟨haB, h⟩
      have : a ∈ conjSubgroup (conjSubgroup (blockU L) t) x ⊓
          conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) t := ⟨ha, haQ⟩
      rwa [P.kf₂.infQ] at this
    · intro h
      exact mc (conjSubgroup (blockU L) t) a fun v hv =>
        P.loc₂.rk.U_comm v hv a (P.loc₂.rk.W_le_U h)
  ·
    have hx₁c := mc (conjSubgroup (conjSubgroup (blockU L) t) x) x₁ fun v hv =>
      (P.comm_U₁x_U₂x x₁ hx₁ v hv).symm
    have hu₁c := mc (conjSubgroup (conjSubgroup (blockU L) t) x) u₁ fun v hv =>
      (P.a_comm_U₁ hv u₁ hu₁).symm
    have hac := mc (conjSubgroup (conjSubgroup (blockU L) t) x) a fun v hv =>
      P.loc₂.rk.conj_comm x v hv a ha
    have hec := mc (conjSubgroup (conjSubgroup (blockU L) t) x) e fun v hv =>
      (P.a_comm_U₁ hv e hWU).symm
    have hfc := mc (conjSubgroup (conjSubgroup (blockU L) t) x) f fun v hv => hfX.2 v hv
    have hR := (centralizer ((conjSubgroup (conjSubgroup (blockU L) t) x : Subgroup G) :
      Set G)).mul_mem hec hfc
    rw [mul_mem_cancel_left hx₁c, mul_mem_cancel_left hu₁c, mul_mem_cancel_left hac,
      mul_mem_cancel_right hR]
    constructor
    · intro h
      have : u₂ ∈ conjSubgroup (blockU L) t ⊓
          centralizer ((conjSubgroup (conjSubgroup (blockU L) t) x : Subgroup G) : Set G) :=
        ⟨hu₂, h⟩
      rwa [P.kf₂.infC] at this
    · intro h
      exact mc (conjSubgroup (conjSubgroup (blockU L) t) x) u₂ fun v hv =>
        P.loc₂.rk.conj_comm x v hv u₂ (P.W₂_le_Y h)

theorem comm_eq_one_of_sq {x₁ u₁ a u₂ e f : G} (hx₁ : x₁ ∈ conjSubgroup (blockU L) x)
    (hu₁ : u₁ ∈ blockU L) (ha : a ∈ conjSubgroup (conjSubgroup (blockU L) t) x)
    (hu₂ : u₂ ∈ conjSubgroup (blockU L) t) (he : e ∈ W) (hf : f ∈ baumD S L)
    (hb2 : (x₁ * (u₁ * (a * (u₂ * (e * f))))) ^ 2 = 1) : ⁅x₁, u₁⁆ = 1 ∧ ⁅a, u₂⁆ = 1 := by
  have hsq := P.sq_B_decomp hx₁ hu₁ ha hu₂ he hf
  rw [hb2] at hsq
  have h1 : ⁅x₁, u₁⁆ = (⁅a, u₂⁆)⁻¹ := eq_inv_of_mul_eq_one_left hsq.symm
  have hm1 := P.comm_mem_W₁ hx₁ hu₁
  have hm2 := P.comm_mem_W₂ ha hu₂
  have hmem : ⁅x₁, u₁⁆ ∈ W ⊓ conjSubgroup W t :=
    ⟨hm1, by rw [h1]; exact (conjSubgroup W t).inv_mem hm2⟩
  rw [P.W_inf_W₂] at hmem
  have e1 : ⁅x₁, u₁⁆ = 1 := Subgroup.mem_bot.1 hmem
  exact ⟨e1, inv_eq_one.1 (h1.symm.trans e1)⟩

theorem dichotomy₁ {b : G} (hb : b ∈ baum S) (hb2 : b ^ 2 = 1) :
    b ∈ centralizer (blockU L : Set G) ∨
      b ∈ centralizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G) := by
  obtain ⟨x₁, hx₁, u₁, hu₁, a, ha, u₂, hu₂, e, he, f, hf, rfl⟩ := P.B_decomp hb
  obtain ⟨hc1, -⟩ := P.comm_eq_one_of_sq hx₁ hu₁ ha hu₂ he hf hb2
  obtain ⟨hU₁, hX₁, -, -⟩ := P.prod_cent hx₁ hu₁ ha hu₂ he hf
  by_cases hxW : x₁ ∈ W
  · exact Or.inl (hU₁.2 hxW)
  · right
    refine hX₁.2 ?_
    have hx₁B : x₁ ∈ baum S := P.kf₁.Ux_le_B hx₁
    have hx₁Q : x₁ ∉ baum S ⊓ centralizer (blockU L : Set G) := by
      intro hQ
      apply hxW
      have : x₁ ∈ conjSubgroup (blockU L) x ⊓ (baum S ⊓ centralizer (blockU L : Set G)) :=
        ⟨hx₁, hQ⟩
      rwa [P.kf₁.infQ] at this
    exact (P.loc.rk.cent_y x₁ hx₁B hx₁Q u₁ hu₁).2
      (commutatorElement_eq_one_iff_mul_comm.1 hc1).symm

theorem dichotomy₂ {b : G} (hb : b ∈ baum S) (hb2 : b ^ 2 = 1) :
    b ∈ centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G) ∨
      b ∈ centralizer ((conjSubgroup (conjSubgroup (blockU L) t) x : Subgroup G) : Set G) := by
  obtain ⟨x₁, hx₁, u₁, hu₁, a, ha, u₂, hu₂, e, he, f, hf, rfl⟩ := P.B_decomp hb
  obtain ⟨-, hc2⟩ := P.comm_eq_one_of_sq hx₁ hu₁ ha hu₂ he hf hb2
  obtain ⟨-, -, hU₂, hX₂⟩ := P.prod_cent hx₁ hu₁ ha hu₂ he hf
  by_cases haW : a ∈ conjSubgroup W t
  · exact Or.inl (hU₂.2 haW)
  · right
    refine hX₂.2 ?_
    have haB : a ∈ baum S := P.kf₂.Ux_le_B ha
    have haQ : a ∉ conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) t := by
      intro hQ
      apply haW
      have : a ∈ conjSubgroup (conjSubgroup (blockU L) t) x ⊓
          conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) t := ⟨ha, hQ⟩
      rwa [P.kf₂.infQ] at this
    exact (P.loc₂.rk.cent_y a haB haQ u₂ hu₂).2
      (commutatorElement_eq_one_iff_mul_comm.1 hc2).symm

theorem elemAb_dichotomy {A : Subgroup G} (hA : ElemAb2 A) (hAB : A ≤ baum S) :
    (A ≤ baum S ⊓ centralizer (blockU L : Set G) ∨
        A ≤ baum S ⊓ centralizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G)) ∧
      (A ≤ baum S ⊓ centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G) ∨
        A ≤ baum S ⊓ centralizer
          ((conjSubgroup (conjSubgroup (blockU L) t) x : Subgroup G) : Set G)) := by
  refine ⟨le_or_le_of_forall_mem_or fun a ha => ?_, le_or_le_of_forall_mem_or fun a ha => ?_⟩
  · rcases P.dichotomy₁ (hAB ha) (hA.sq_eq_one ha) with h | h
    · exact Or.inl ⟨hAB ha, h⟩
    · exact Or.inr ⟨hAB ha, h⟩
  · rcases P.dichotomy₂ (hAB ha) (hA.sq_eq_one ha) with h | h
    · exact Or.inl ⟨hAB ha, h⟩
    · exact Or.inr ⟨hAB ha, h⟩

end Setup

end CFSG.QuasithinUnique.AppE
