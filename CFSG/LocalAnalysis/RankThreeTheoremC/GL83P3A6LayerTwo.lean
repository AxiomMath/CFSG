module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerFrame
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Core

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer

open CFSG.Open Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux
  CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Mod

section PMSec

variable {X : Type} [Group X]

def PM (y a : X) : Prop := y = a ∨ y = a⁻¹

theorem PM.cj {g h y a b : X} (h1 : PM (h * y * h⁻¹) a) (h2 : PM (g * a * g⁻¹) b) :
    PM ((g * h) * y * (g * h)⁻¹) b := by
  have e : (g * h) * y * (g * h)⁻¹ = g * (h * y * h⁻¹) * g⁻¹ := by group
  rw [e]
  rcases h1 with h1 | h1 <;> rw [h1]
  · exact h2
  · have e2 : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e2]
    rcases h2 with h2 | h2 <;> rw [h2]
    · exact Or.inr rfl
    · exact Or.inl (inv_inv b)

theorem PM.sq {h y : X} (h1 : PM (h * y * h⁻¹) y) : (h * h) * y * (h * h)⁻¹ = y := by
  have e : (h * h) * y * (h * h)⁻¹ = h * (h * y * h⁻¹) * h⁻¹ := by group
  rw [e]
  rcases h1 with h1 | h1 <;> rw [h1]
  · exact h1
  · have e2 : h * y⁻¹ * h⁻¹ = (h * y * h⁻¹)⁻¹ := by group
    rw [e2, h1, inv_inv]

theorem PM.one (y : X) : PM (1 * y * 1⁻¹) y := Or.inl (by group)

theorem PM.zpow {y : X} {s : ℤ} (hs : s = 1 ∨ s = -1) : PM (y ^ s) y := by
  rcases hs with rfl | rfl
  · exact Or.inl (zpow_one y)
  · exact Or.inr (zpow_neg_one y)

theorem PM.zpow_neg {y : X} {s : ℤ} (hs : s = 1 ∨ s = -1) : PM (y ^ (-s)) y :=
  PM.zpow (by rcases hs with rfl | rfl <;> simp)

end PMSec

namespace XFrame

variable {X : Type} [Group X] [Finite X] {x e₂ e₃ t ρ : X} {s : ℤ}
  (h : XFrame x e₂ e₃ t ρ s)

def Diag (x e₂ e₃ g : X) : Prop :=
  PM (g * x * g⁻¹) x ∧ PM (g * e₂ * g⁻¹) e₂ ∧ PM (g * e₃ * g⁻¹) e₃

def Swap (x e₂ e₃ g : X) : Prop :=
  PM (g * x * g⁻¹) x ∧ PM (g * e₂ * g⁻¹) e₃ ∧ PM (g * e₃ * g⁻¹) e₂

def Mono (x e₂ e₃ g : X) : Prop := Diag x e₂ e₃ g ∨ Swap x e₂ e₃ g

theorem mono_mul {g k : X} (hg : Mono x e₂ e₃ g) (hk : Mono x e₂ e₃ k) :
    (Diag x e₂ e₃ g → Diag x e₂ e₃ k → Diag x e₂ e₃ (g * k)) ∧
    (Diag x e₂ e₃ g → Swap x e₂ e₃ k → Swap x e₂ e₃ (g * k)) ∧
    (Swap x e₂ e₃ g → Diag x e₂ e₃ k → Swap x e₂ e₃ (g * k)) ∧
    (Swap x e₂ e₃ g → Swap x e₂ e₃ k → Diag x e₂ e₃ (g * k)) := by
  refine ⟨fun ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ => ⟨b1.cj a1, b2.cj a2, b3.cj a3⟩,
    fun ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ => ⟨b1.cj a1, b2.cj a3, b3.cj a2⟩,
    fun ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ => ⟨b1.cj a1, b2.cj a2, b3.cj a3⟩,
    fun ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ => ⟨b1.cj a1, b2.cj a3, b3.cj a2⟩⟩

theorem Mono.mul {g k : X} (hg : Mono x e₂ e₃ g) (hk : Mono x e₂ e₃ k) :
    Mono x e₂ e₃ (g * k) := by
  obtain ⟨h1, h2, h3, h4⟩ := mono_mul hg hk
  rcases hg with hg | hg <;> rcases hk with hk | hk
  · exact Or.inl (h1 hg hk)
  · exact Or.inr (h2 hg hk)
  · exact Or.inr (h3 hg hk)
  · exact Or.inl (h4 hg hk)

theorem Mono.sq {g : X} (hg : Mono x e₂ e₃ g) : Diag x e₂ e₃ (g * g) := by
  obtain ⟨h1, -, -, h4⟩ := mono_mul hg hg
  rcases hg with hg | hg
  · exact h1 hg hg
  · exact h4 hg hg

theorem mono_one : Mono x e₂ e₃ 1 := Or.inl ⟨PM.one x, PM.one e₂, PM.one e₃⟩

theorem Mono.pow {g : X} (hg : Mono x e₂ e₃ g) (n : ℕ) : Mono x e₂ e₃ (g ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact mono_one
  | succ n ih => rw [pow_succ]; exact ih.mul hg

def monoSub (x e₂ e₃ : X) : Subgroup X where
  carrier := {g | Mono x e₂ e₃ g}
  mul_mem' := fun ha hb => Mono.mul ha hb
  one_mem' := mono_one
  inv_mem' := by
    intro g hg
    have hpos : 0 < orderOf g := orderOf_pos g
    have hinv : g⁻¹ = g ^ (orderOf g - 1) := by
      refine (eq_inv_of_mul_eq_one_right ?_).symm
      rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    show Mono x e₂ e₃ g⁻¹
    rw [hinv]
    exact Mono.pow hg _

include h

theorem diag_sq_mem {g : X} (hg : Diag x e₂ e₃ g) :
    g * g ∈ centralizer ((Qf x e₂ e₃ : Subgroup X) : Set X) := by
  obtain ⟨h1, h2, h3⟩ := hg
  have key : ∀ y : X, (g * g) * y * (g * g)⁻¹ = y → y ∈ centralizer ({g * g} : Set X) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    calc y * (g * g) = ((g * g) * y * (g * g)⁻¹) * (g * g) := by rw [hy]
      _ = g * g * y := by group
  have hle : Qf x e₂ e₃ ≤ centralizer ({g * g} : Set X) :=
    h.Q_le_of_mem (key x h1.sq) (key e₂ h2.sq) (key e₃ h3.sq)
  rw [mem_centralizer_iff]
  intro q hq
  exact mem_centralizer_singleton_iff.mp (hle hq)

theorem mono_mem_normalizer {g : X} (hg : Mono x e₂ e₃ g) :
    g ∈ normalizer ((Qf x e₂ e₃ : Subgroup X) : Set X) := by
  apply GL83P3A6Core.mem_normalizer_of_map_le
  rw [Subgroup.map_le_iff_le_comap]
  have hPM : ∀ y a : X, a ∈ Qf x e₂ e₃ → PM (g * y * g⁻¹) a →
      y ∈ (Qf x e₂ e₃).comap (MulAut.conj g).toMonoidHom := by
    intro y a ha hy
    rw [Subgroup.mem_comap]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases hy with hy | hy <;> rw [hy]
    · exact ha
    · exact inv_mem ha
  rcases hg with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact h.Q_le_of_mem (hPM x x h.x_mem h1) (hPM e₂ e₂ h.e₂_mem h2) (hPM e₃ e₃ h.e₃_mem h3)
  · exact h.Q_le_of_mem (hPM x x h.x_mem h1) (hPM e₂ e₃ h.e₃_mem h2) (hPM e₃ e₂ h.e₂_mem h3)

theorem monoSub_le : monoSub x e₂ e₃ ≤ normalizer ((Qf x e₂ e₃ : Subgroup X) : Set X) :=
  fun _ hg => h.mono_mem_normalizer hg

theorem ρ_mono : Mono x e₂ e₃ ρ := by
  refine Or.inr ⟨Or.inl h.ρ_x, ?_, ?_⟩
  · rw [h.ρ_e₂]; exact PM.zpow h.s_cases
  · rw [h.ρ_e₃]; exact PM.zpow_neg h.s_cases

theorem d_conj (a b c : ZMod 3) :
    (t * (ρ * ρ) * t⁻¹) * qel x e₂ e₃ (a, b, c) * (t * (ρ * ρ) * t⁻¹)⁻¹ =
      qel x e₂ e₃ (-a, b, -c) :=
  h.frame3.conj_g2 a b c

theorem qel_eq_inv {v w : Vec} (hvw : v + w = 0) : qel x e₂ e₃ v = (qel x e₂ e₃ w)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← h.frame3.qel_add, hvw, h.frame3.qel_zero]

theorem d_mono : Mono x e₂ e₃ (t * (ρ * ρ) * t⁻¹) := by
  have hx := h.d_conj 1 0 0
  have h2 := h.d_conj 0 1 0
  have h3 := h.d_conj 0 0 1
  rw [h.qel_x] at hx
  rw [h.qel_e₂] at h2
  rw [h.qel_e₃] at h3
  refine Or.inl ⟨Or.inr ?_, Or.inl ?_, Or.inr ?_⟩
  · rw [hx, h.qel_eq_inv (w := (1, 0, 0)) (by decide), h.qel_x]
  · rw [h2, show ((-0, 1, -0) : Vec) = (0, 1, 0) by decide, h.qel_e₂]
  · rw [h3, h.qel_eq_inv (w := (0, 0, 1)) (by decide), h.qel_e₃]

theorem conj_eq_of_inv_mul_mem {g g' : X} (hgN : g ∈ normalizer ((Qf x e₂ e₃ : Subgroup X) : Set X))
    (hc : g⁻¹ * g' ∈ centralizer ((Qf x e₂ e₃ : Subgroup X) : Set X)) {q : X}
    (hq : q ∈ Qf x e₂ e₃) :
    g' * q * g'⁻¹ = g * q * g⁻¹ ∧ g'⁻¹ * q * g' = g⁻¹ * q * g := by
  have hcq : q * (g⁻¹ * g') = (g⁻¹ * g') * q := (mem_centralizer_iff.mp hc) q hq
  have hq' : g⁻¹ * q * g ∈ Qf x e₂ e₃ := by
    have := (mem_normalizer_iff.mp ((normalizer _).inv_mem hgN) q).mp hq
    simpa using this
  have hcq' : (g⁻¹ * q * g) * (g⁻¹ * g') = (g⁻¹ * g') * (g⁻¹ * q * g) :=
    (mem_centralizer_iff.mp hc) _ hq'
  constructor
  · calc g' * q * g'⁻¹ = g * ((g⁻¹ * g') * q) * (g⁻¹ * g')⁻¹ * g⁻¹ := by group
      _ = g * (q * (g⁻¹ * g')) * (g⁻¹ * g')⁻¹ * g⁻¹ := by rw [hcq]
      _ = g * q * g⁻¹ := by group
  · calc g'⁻¹ * q * g' = (g⁻¹ * g')⁻¹ * ((g⁻¹ * q * g) * (g⁻¹ * g')) := by group
      _ = (g⁻¹ * g')⁻¹ * ((g⁻¹ * g') * (g⁻¹ * q * g)) := by rw [hcq']
      _ = g⁻¹ * q * g := by group

theorem ρ_inv_conj (a b c : ZMod 3) :
    ρ⁻¹ * qel x e₂ e₃ (a, b, c) * ρ = qel x e₂ e₃ (a, (s : ZMod 3) * c, -((s : ZMod 3) * b)) := by
  have hF := h.frame3
  have e := hF.conj_ρ a ((s : ZMod 3) * c) (-((s : ZMod 3) * b))
  have hs := hF.sv_sq
  have hv : ∀ σ a b c : ZMod 3, σ * σ = 1 →
      ((a, -(σ * -(σ * b)), σ * (σ * c)) : Vec) = (a, b, c) := by decide
  rw [hv _ a b c hs] at e
  rw [← e]
  group

theorem d_inv_conj (a b c : ZMod 3) :
    (t * (ρ * ρ) * t⁻¹)⁻¹ * qel x e₂ e₃ (a, b, c) * (t * (ρ * ρ) * t⁻¹) =
      qel x e₂ e₃ (-a, b, -c) := by
  have e := h.d_conj (-a) b (-c)
  have hv : ∀ a b c : ZMod 3, ((- -a, b, - -c) : Vec) = (a, b, c) := by decide
  rw [hv] at e
  rw [← e]
  group

theorem comm_not_mem {τ₁ τ₂ : X}
    (h₁ : ρ⁻¹ * τ₁ ∈ centralizer ((Qf x e₂ e₃ : Subgroup X) : Set X))
    (h₂ : (t * (ρ * ρ) * t⁻¹)⁻¹ * τ₂ ∈ centralizer ((Qf x e₂ e₃ : Subgroup X) : Set X)) :
    τ₁ * τ₂ * τ₁⁻¹ * τ₂⁻¹ ∉ centralizer ((Qf x e₂ e₃ : Subgroup X) : Set X) := by
  intro hc
  have hρN := h.ρ_mem_normalizer
  have hdN : t * (ρ * ρ) * t⁻¹ ∈ normalizer ((Qf x e₂ e₃ : Subgroup X) : Set X) :=
    h.mono_mem_normalizer h.d_mono
  have hs := h.frame3.sv_sq
  have s1 : τ₂⁻¹ * qel x e₂ e₃ (0, 1, 0) * τ₂ = qel x e₂ e₃ (0, 1, 0) := by
    rw [(h.conj_eq_of_inv_mul_mem hdN h₂ (h.qel_mem _)).2, h.d_inv_conj,
      show ((-0, 1, -0) : Vec) = (0, 1, 0) by decide]
  have s2 : τ₁⁻¹ * qel x e₂ e₃ (0, 1, 0) * τ₁ = qel x e₂ e₃ (0, 0, -(s : ZMod 3)) := by
    rw [(h.conj_eq_of_inv_mul_mem hρN h₁ (h.qel_mem _)).2, h.ρ_inv_conj]
    have hv : ∀ σ : ZMod 3, ((0, σ * 0, -(σ * 1)) : Vec) = (0, 0, -σ) := by decide
    rw [hv]
  have s3 : τ₂ * qel x e₂ e₃ (0, 0, -(s : ZMod 3)) * τ₂⁻¹ = qel x e₂ e₃ (0, 0, (s : ZMod 3)) := by
    rw [(h.conj_eq_of_inv_mul_mem hdN h₂ (h.qel_mem _)).1, h.d_conj]
    have hv : ∀ σ : ZMod 3, ((-0, 0, - -σ) : Vec) = (0, 0, σ) := by decide
    rw [hv]
  have s4 : τ₁ * qel x e₂ e₃ (0, 0, (s : ZMod 3)) * τ₁⁻¹ = qel x e₂ e₃ (0, -1, 0) := by
    rw [(h.conj_eq_of_inv_mul_mem hρN h₁ (h.qel_mem _)).1, h.frame3.conj_ρ]
    have hv : ∀ σ : ZMod 3, σ * σ = 1 → ((0, -(σ * σ), σ * 0) : Vec) = (0, -1, 0) := by decide
    rw [hv _ hs]
  have hcomm := (mem_centralizer_iff.mp hc) _ (h.qel_mem (0, 1, 0))
  have hfix : (τ₁ * τ₂ * τ₁⁻¹ * τ₂⁻¹) * qel x e₂ e₃ (0, 1, 0) *
      (τ₁ * τ₂ * τ₁⁻¹ * τ₂⁻¹)⁻¹ = qel x e₂ e₃ (0, 1, 0) := by
    rw [← hcomm]; group
  have e : (τ₁ * τ₂ * τ₁⁻¹ * τ₂⁻¹) * qel x e₂ e₃ (0, 1, 0) * (τ₁ * τ₂ * τ₁⁻¹ * τ₂⁻¹)⁻¹ =
      τ₁ * (τ₂ * (τ₁⁻¹ * (τ₂⁻¹ * qel x e₂ e₃ (0, 1, 0) * τ₂) * τ₁) * τ₂⁻¹) * τ₁⁻¹ := by group
  rw [e, s1, s2, s3, s4] at hfix
  have := h.qel_inj hfix
  revert this
  decide

theorem exists_sylow_comm (S : Subgroup X)
    (hS : IsSylowOf 2 S (normalizer ((Qf x e₂ e₃ : Subgroup X) : Set X))) :
    ∃ a ∈ S, ∃ b ∈ S,
      a * b * a⁻¹ * b⁻¹ ∉ centralizer ((Qf x e₂ e₃ : Subgroup X) : Set X) := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup X := centralizer ((Qf x e₂ e₃ : Subgroup X) : Set X) with hC
  set N : Subgroup X := normalizer ((Qf x e₂ e₃ : Subgroup X) : Set X) with hN
  set Sm : Subgroup X := monoSub x e₂ e₃ with hSm
  have hSmN : Sm ≤ N := h.monoSub_le
  set K : Subgroup ↥Sm := C.subgroupOf Sm with hK
  have hKn : K.Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [hK, mem_subgroupOf] at hk ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_centralizer_aux (hSmN g.2) hk
  have h4 : ∀ g : ↥Sm, g ^ 4 ∈ K := by
    intro g
    have hsq := h.diag_sq_mem (Mono.sq g.2)
    rw [hK, mem_subgroupOf]
    have e : ((g ^ 4 : ↥Sm) : X) = ((g : X) * g) * ((g : X) * g) := by
      simp only [SubgroupClass.coe_pow, MulMemClass.coe_mul, pow_succ, pow_zero, one_mul,
        mul_assoc]
    rw [e]
    exact hsq
  have hp : IsPGroup 2 (↥Sm ⧸ K) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨2, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact h4 g
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥Sm) := inferInstance
  set T' : Sylow 2 (↥Sm ⧸ K) := T.mapSurjective (QuotientGroup.mk'_surjective K) with hT'
  have hTtop : (T' : Subgroup (↥Sm ⧸ K)) = ⊤ := (T'.3 (hp.to_subgroup ⊤) le_top).symm
  have hcover : ∀ g : ↥Sm, ∃ τ ∈ (T : Subgroup ↥Sm), (τ : X)⁻¹ * g ∈ C := by
    intro g
    have hmem : QuotientGroup.mk' K g ∈ (T' : Subgroup (↥Sm ⧸ K)) := by
      rw [hTtop]; exact mem_top _
    rw [hT', Sylow.coe_mapSurjective] at hmem
    obtain ⟨τ, hτ, hτg⟩ := hmem
    refine ⟨τ, hτ, ?_⟩
    have := QuotientGroup.eq.mp hτg
    rw [hK, mem_subgroupOf] at this
    simpa using this
  obtain ⟨τ₁, hτ₁, hc₁⟩ := hcover ⟨ρ, h.ρ_mono⟩
  obtain ⟨τ₂, hτ₂, hc₂⟩ := hcover ⟨t * (ρ * ρ) * t⁻¹, h.d_mono⟩
  have hc₁' : ρ⁻¹ * (τ₁ : X) ∈ C := by
    have := C.inv_mem hc₁
    simpa using this
  have hc₂' : (t * (ρ * ρ) * t⁻¹)⁻¹ * (τ₂ : X) ∈ C := by
    have := C.inv_mem hc₂
    simpa using this
  have hnot := h.comm_not_mem hc₁' hc₂'
  set T₀ : Subgroup X := (T : Subgroup ↥Sm).map Sm.subtype with hT₀
  have hT₀2 : IsPGroup 2 T₀ := T.isPGroup'.map _
  have hT₀N : T₀ ≤ N := (Subgroup.map_subtype_le _).trans hSmN
  obtain ⟨P₀, hP₀⟩ := (hT₀2.comap_subtype (K := N)).exists_le_sylow
  have hS₀ : IsSylowOf 2 ((P₀ : Subgroup ↥N).map N.subtype) N := ⟨P₀, rfl⟩
  have hT₀S₀ : T₀ ≤ (P₀ : Subgroup ↥N).map N.subtype := by
    intro y hy
    exact ⟨⟨y, hT₀N hy⟩, hP₀ hy, rfl⟩
  obtain ⟨k, hkN, hk⟩ := hS.exists_mem_conj hS₀
  have hτ₁S₀ : (τ₁ : X) ∈ (P₀ : Subgroup ↥N).map N.subtype := hT₀S₀ ⟨τ₁, hτ₁, rfl⟩
  have hτ₂S₀ : (τ₂ : X) ∈ (P₀ : Subgroup ↥N).map N.subtype := hT₀S₀ ⟨τ₂, hτ₂, rfl⟩
  refine ⟨k⁻¹ * τ₁ * k, (hk _).mp hτ₁S₀, k⁻¹ * τ₂ * k, (hk _).mp hτ₂S₀, fun hmem => hnot ?_⟩
  have e : (τ₁ : X) * τ₂ * (τ₁ : X)⁻¹ * (τ₂ : X)⁻¹ =
      k * ((k⁻¹ * τ₁ * k) * (k⁻¹ * τ₂ * k) * (k⁻¹ * τ₁ * k)⁻¹ * (k⁻¹ * τ₂ * k)⁻¹) * k⁻¹ := by
    group
  rw [e]
  exact conj_mem_centralizer_aux hkN hmem

end XFrame

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer
