module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ModIsoAct
public import CFSG.LargeExtraspecial.S45QLin

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.OddStandard.AltStdSmall4.W49

open Subgroup Equiv ModIso
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
open scoped Pointwise commutatorElement

section GL3

theorem isSimpleGroup_GL3 : IsSimpleGroup (GL (Fin 3) (ZMod 2)) :=
  CFSG.LargeExtraspecial.S45Q.isSimpleGroup_GL_zmod_two le_rfl

@[expose] def glInv (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : M * M = 1) :
    GL (Fin 3) (ZMod 2) :=
  ⟨M, M, h, h⟩

@[expose] def t01 : GL (Fin 3) (ZMod 2) := glInv !![1, 1, 0; 0, 1, 0; 0, 0, 1] (by decide)

@[expose] def t12 : GL (Fin 3) (ZMod 2) := glInv !![1, 0, 0; 0, 1, 1; 0, 0, 1] (by decide)

@[expose] def t21 : GL (Fin 3) (ZMod 2) := glInv !![1, 0, 0; 0, 1, 0; 0, 1, 1] (by decide)

@[expose] def t10 : GL (Fin 3) (ZMod 2) := glInv !![1, 0, 0; 1, 1, 0; 0, 0, 1] (by decide)

theorem t01_mul_self : t01 * t01 = 1 := Units.ext (by decide)

theorem eq_zero_of_linPerm8_fix : ∀ v : Fin 8, linPerm8 t01 v = v → linPerm8 t12 v = v →
    linPerm8 t10 v = v → v = 0 := by
  decide +kernel

theorem t01_ne_one : t01 ≠ 1 := fun h => by
  have h1 := congrArg (fun A : GL (Fin 3) (ZMod 2) => (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1) h
  revert h1
  decide

theorem commutator_GL3 :
    ⁅(⊤ : Subgroup (GL (Fin 3) (ZMod 2))), (⊤ : Subgroup (GL (Fin 3) (ZMod 2)))⁆ = ⊤ := by
  have := isSimpleGroup_GL3
  rcases this.eq_bot_or_eq_top_of_normal
    ⁅(⊤ : Subgroup (GL (Fin 3) (ZMod 2))), (⊤ : Subgroup (GL (Fin 3) (ZMod 2)))⁆ with h | h
  · exfalso
    have h1 : ⁅t01, t12⁆ ∈
        ⁅(⊤ : Subgroup (GL (Fin 3) (ZMod 2))), (⊤ : Subgroup (GL (Fin 3) (ZMod 2)))⁆ :=
      commutator_mem_commutator (mem_top _) (mem_top _)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    have h2 := congrArg (fun A : GL (Fin 3) (ZMod 2) => (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2)
      h1
    revert h2
    decide
  · exact h

theorem eq_top_of_involutions {S : Subgroup (GL (Fin 3) (ZMod 2))}
    (hS : ∀ A : GL (Fin 3) (ZMod 2), A * A = 1 → A ∈ S) : S = ⊤ := by
  have hsimple := isSimpleGroup_GL3
  have hle : normalClosure ({t01} : Set (GL (Fin 3) (ZMod 2))) ≤ S := by
    refine closure_le _ |>.2 fun A hA => hS A ?_
    obtain ⟨B, hB, hBA⟩ := Group.mem_conjugatesOfSet_iff.1 hA
    rw [Set.mem_singleton_iff] at hB
    subst hB
    obtain ⟨c, hc⟩ := isConj_iff.1 hBA
    rw [← hc]
    calc c * t01 * c⁻¹ * (c * t01 * c⁻¹) = c * (t01 * t01) * c⁻¹ := by group
      _ = 1 := by rw [t01_mul_self]; group
  rcases hsimple.eq_bot_or_eq_top_of_normal (normalClosure ({t01} : Set (GL (Fin 3) (ZMod 2))))
    with h | h
  · exfalso
    have h1 : t01 ∈ normalClosure ({t01} : Set (GL (Fin 3) (ZMod 2))) :=
      subset_normalClosure (Set.mem_singleton t01)
    rw [h, mem_bot] at h1
    exact t01_ne_one h1
  · exact eq_top_iff.2 (h ▸ hle)

theorem eq_top_of_normal_t01 {S : Subgroup (GL (Fin 3) (ZMod 2))} (hS : S.Normal)
    (h : t01 ∈ S) : S = ⊤ := by
  haveI := hS
  rcases isSimpleGroup_GL3.eq_bot_or_eq_top_of_normal S with h' | h'
  · rw [h', mem_bot] at h
    exact absurd h t01_ne_one
  · exact h'

end GL3

section Conj

variable {G : Type} [Group G]

theorem commutator_le_self (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)

theorem mem_conjSub_iff {g x : G} {X : Subgroup G} :
    x ∈ conjSub g X ↔ g⁻¹ * x * g ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem card_sup_of_inf_eq_bot {A B : Subgroup G} (hB : B ≤ normalizer (A : Set G))
    (hAB : A ⊓ B = ⊥) : Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left A B hB
  let f : A × B → (A ⊔ B : Subgroup G) := fun p =>
    ⟨p.1 * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
      have h2 : (a' : G)⁻¹ * a ∈ A ⊓ B := by
        refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem a'.2) a.2, ?_⟩
        have : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
          calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
            _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
            _ = b' * (b : G)⁻¹ := by group
        rw [this]
        exact mul_mem b'.2 (inv_mem b.2)
      rw [hAB, mem_bot] at h2
      have ha : (a : G) = a' := by
        calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
          _ = a' := by rw [h2, mul_one]
      have hb : (b : G) = b' := by
        rw [ha] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (A : Set G) * (B : Set G) := by
        rw [← hm]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod]

private theorem exists_conj_eq_of_sylow [Finite G] {T O : Subgroup G}
    (hTN : T ≤ normalizer (O : Set G)) (hT : IsPGroup 2 T) (hO : Nat.Coprime 2 (Nat.card O))
    (S : Sylow 2 ↥(T ⊔ O)) :
    ∃ o ∈ O, (S : Subgroup ↥(T ⊔ O)).map (T ⊔ O).subtype = conjSub o T := by
  obtain ⟨a, ha⟩ := hT.exists_card_eq
  have hOT : O ⊓ T = ⊥ :=
    inf_eq_bot_of_coprime (by rw [ha]; exact (Nat.Coprime.pow_left a hO).symm)
  have hcard : Nat.card ↥(T ⊔ O) = Nat.card T * Nat.card O := by
    rw [sup_comm, card_sup_of_inf_eq_bot hTN hOT, mul_comm]
  have hTK : T ≤ T ⊔ O := le_sup_left
  have hT' : IsPGroup 2 (T.subgroupOf (T ⊔ O)) := hT.of_equiv (subgroupOfEquivOfLe hTK).symm
  have hidx : ¬ 2 ∣ (T.subgroupOf (T ⊔ O)).index := by
    have h1 := Subgroup.card_mul_index (T.subgroupOf (T ⊔ O))
    rw [Nat.card_congr (subgroupOfEquivOfLe hTK).toEquiv, hcard] at h1
    have h2 : (T.subgroupOf (T ⊔ O)).index = Nat.card O :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    rw [h2]
    obtain ⟨m, hm⟩ := Nat.coprime_two_left.1 hO
    omega
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥(T ⊔ O) (hT'.toSylow hidx) S
  have hmemS : ∀ x : ↥(T ⊔ O), x ∈ (S : Subgroup ↥(T ⊔ O)) ↔ (k : G)⁻¹ * x * k ∈ T := by
    intro x
    rw [← hk, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, mem_pointwise_smul_iff_inv_smul_mem,
      mem_subgroupOf, MulAut.smul_def, MulAut.conj_inv_apply]
    rfl
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left O T hTN
  have hk' : (k : G) ∈ (O : Set G) * (T : Set G) := by
    rw [← hm, sup_comm]
    exact k.2
  obtain ⟨o, ho, t, ht, hot⟩ := Set.mem_mul.1 hk'
  refine ⟨o, ho, ?_⟩
  ext y
  rw [mem_conjSub_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := (hmemS x).1 hx
    rw [← hot] at hx'
    have : o⁻¹ * (T ⊔ O).subtype x * o = t * ((o * t)⁻¹ * x * (o * t)) * t⁻¹ := by
      rw [Subgroup.coe_subtype]
      group
    rw [this]
    exact mul_mem (mul_mem ht hx') (inv_mem ht)
  · intro hy
    have hyK : y ∈ T ⊔ O := by
      have : y = o * (o⁻¹ * y * o) * o⁻¹ := by group
      rw [this]
      exact mul_mem (mul_mem (mem_sup_right ho) (mem_sup_left hy)) (inv_mem (mem_sup_right ho))
    refine ⟨⟨y, hyK⟩, (hmemS _).2 ?_, rfl⟩
    rw [← hot]
    show (o * t)⁻¹ * y * (o * t) ∈ T
    have : (o * t)⁻¹ * y * (o * t) = t⁻¹ * (o⁻¹ * y * o) * t := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem ht) hy) ht

private theorem exists_cent_conj {O T : Subgroup G} {z o : G} (hz : z * z = 1)
    (hzO : ∀ x ∈ O, z * x * z⁻¹ ∈ O) (hO : ∀ x ∈ O, Odd (orderOf x))
    (hzT : z ∈ normalizer (T : Set G)) (ho : o ∈ O)
    (hzT' : z ∈ normalizer (conjSub o T : Set G)) :
    ∃ c ∈ O, c * z = z * c ∧ conjSub c T = conjSub o T := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hz'T : o⁻¹ * z * o ∈ normalizer (T : Set G) := by
    rw [mem_normalizer_iff]
    intro t
    have h1 := (mem_normalizer_iff.1 hzT') (o * t * o⁻¹)
    rw [mem_conjSub_iff, mem_conjSub_iff] at h1
    have e1 : o⁻¹ * (o * t * o⁻¹) * o = t := by group
    have e2 : o⁻¹ * (z * (o * t * o⁻¹) * z⁻¹) * o = o⁻¹ * z * o * t * (o⁻¹ * z * o)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1
  obtain ⟨u, hu⟩ : ∃ u, u = o⁻¹ * z * o * z := ⟨_, rfl⟩
  have huO : u ∈ O := by
    have : u = o⁻¹ * (z * o * z⁻¹) := by
      rw [hu, hzi]
      group
    rw [this]
    exact mul_mem (inv_mem ho) (hzO o ho)
  have huT : u ∈ normalizer (T : Set G) := by
    rw [hu]
    exact mul_mem hz'T hzT
  have hinv : z * u * z⁻¹ = u⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    calc u * (z * u * z⁻¹) = o⁻¹ * z * o * (z * z) * o⁻¹ * z * o := by
          rw [hu]
          group
      _ = o⁻¹ * z * o * 1 * o⁻¹ * z * o := by rw [hz]
      _ = o⁻¹ * (z * z) * o := by group
      _ = 1 := by
          rw [hz]
          group
  obtain ⟨k, hk⟩ := hO u huO
  have hu1 : u ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one u
  obtain ⟨r, hr⟩ : ∃ r, r = u ^ (k + 1) := ⟨_, rfl⟩
  have hrO : r ∈ O := by
    rw [hr]
    exact pow_mem huO _
  have hrT : r ∈ normalizer (T : Set G) := by
    rw [hr]
    exact pow_mem huT _
  have hzr : z * r * z⁻¹ = r⁻¹ := by
    rw [hr, ← MulAut.conj_apply, map_pow, MulAut.conj_apply, hinv, inv_pow]
  have hzr' : z * r⁻¹ = r * z := by
    have h2 : z * r⁻¹ * z⁻¹ = r := by
      calc z * r⁻¹ * z⁻¹ = (z * r * z⁻¹)⁻¹ := by group
        _ = r := by rw [hzr, inv_inv]
    calc z * r⁻¹ = z * r⁻¹ * z⁻¹ * z := by group
      _ = r * z := by rw [h2]
  have hrr : r * r = u := by
    rw [hr, ← pow_add, show k + 1 + (k + 1) = 2 * k + 1 + 1 by ring, pow_succ u (2 * k + 1),
      hu1, one_mul]
  have hrz : r * z * r⁻¹ = o⁻¹ * z * o := by
    calc r * z * r⁻¹ = r * (z * r⁻¹) := by group
      _ = r * (r * z) := by rw [hzr']
      _ = r * r * z := by group
      _ = u * z := by rw [hrr]
      _ = o⁻¹ * z * o * (z * z) := by
          rw [hu]
          group
      _ = o⁻¹ * z * o := by rw [hz, mul_one]
  refine ⟨o * r, mul_mem ho hrO, ?_, ?_⟩
  · have h3 : o * r * z * (o * r)⁻¹ = z := by
      calc o * r * z * (o * r)⁻¹ = o * (r * z * r⁻¹) * o⁻¹ := by group
        _ = z := by
            rw [hrz]
            group
    calc o * r * z = o * r * z * (o * r)⁻¹ * (o * r) := by group
      _ = z * (o * r) := by rw [h3]
  · ext y
    rw [mem_conjSub_iff, mem_conjSub_iff]
    have e : (o * r)⁻¹ * y * (o * r) = r⁻¹ * (o⁻¹ * y * o) * r := by group
    rw [e]
    exact ((mem_normalizer_iff''.1 hrT) (o⁻¹ * y * o)).symm

end Conj

section Dsub

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

@[expose] def Dsub (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) : Subgroup G :=
  E θ hn ⊔ (kap θ hn).range

variable (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n)

theorem kap_conj_mem_E (A : GL (Fin 3) (ZMod 2)) {x : G} (hx : x ∈ E θ hn) :
    kap θ hn A * x * (kap θ hn A)⁻¹ ∈ E θ hn := by
  obtain ⟨v, rfl⟩ := (N0.mem_E_iff θ hn x).1 hx
  rw [kap_conj_eps]
  exact N0.eps_mem_E θ hn _

theorem range_kap_le_normalizer : (kap θ hn).range ≤ normalizer (E θ hn : Set G) :=
  le_normalizer_of_conj' fun g hg x hx => by
    obtain ⟨A, rfl⟩ := hg
    exact kap_conj_mem_E θ hn A hx

theorem mem_Dsub_iff (x : G) :
    x ∈ Dsub θ hn ↔ ∃ (v : Fin 8) (A : GL (Fin 3) (ZMod 2)), x = N0.eps θ hn v * kap θ hn A := by
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left (E θ hn) (kap θ hn).range
    (range_kap_le_normalizer θ hn)
  constructor
  · intro hx
    have hx' : x ∈ ((E θ hn : Set G) * ((kap θ hn).range : Set G)) := by
      rw [← hm]
      exact hx
    obtain ⟨a, ha, b, ⟨A, rfl⟩, rfl⟩ := Set.mem_mul.1 hx'
    obtain ⟨v, rfl⟩ := (N0.mem_E_iff θ hn a).1 ha
    exact ⟨v, A, rfl⟩
  · rintro ⟨v, A, rfl⟩
    exact mul_mem (mem_sup_left (N0.eps_mem_E θ hn v)) (mem_sup_right ⟨A, rfl⟩)

theorem eps_mem_Dsub (v : Fin 8) : N0.eps θ hn v ∈ Dsub θ hn :=
  mem_sup_left (N0.eps_mem_E θ hn v)

theorem kap_mem_Dsub (A : GL (Fin 3) (ZMod 2)) : kap θ hn A ∈ Dsub θ hn :=
  mem_sup_right ⟨A, rfl⟩

theorem E_le_Dsub : E θ hn ≤ Dsub θ hn := le_sup_left

theorem Dsub_le_L : Dsub θ hn ≤ L :=
  sup_le (E_le_L hn) (by rintro _ ⟨A, rfl⟩; exact kap_mem_L θ hn A)

theorem eps_xr_eq_comm (A : GL (Fin 3) (ZMod 2)) (u : Fin 8) :
    N0.eps θ hn (xr (linPerm8 A u) u) =
      kap θ hn A * N0.eps θ hn u * (kap θ hn A)⁻¹ * (N0.eps θ hn u)⁻¹ := by
  rw [kap_conj_eps, N0.eps_inv, N0.eps_mul, N0.xr_eq_xor]

theorem Dsub_le_of_conj {M : Subgroup G} (hM : ∀ d ∈ Dsub θ hn, ∀ m ∈ M, d * m * d⁻¹ ∈ M)
    (h0 : kap θ hn t01 ∈ M) : Dsub θ hn ≤ M := by
  have hK : M.comap (kap θ hn) = ⊤ := by
    refine eq_top_of_normal_t01 ⟨fun A hA B => ?_⟩ h0
    rw [mem_comap, map_mul, map_mul, map_inv]
    exact hM _ (kap_mem_Dsub θ hn B) _ hA
  have hkap : ∀ A, kap θ hn A ∈ M := fun A => by
    have : A ∈ M.comap (kap θ hn) := by rw [hK]; exact mem_top A
    exact this
  have hcomm : ∀ A u, N0.eps θ hn (xr (linPerm8 A u) u) ∈ M := by
    intro A u
    rw [eps_xr_eq_comm, show kap θ hn A * N0.eps θ hn u * (kap θ hn A)⁻¹ * (N0.eps θ hn u)⁻¹ =
      kap θ hn A * (N0.eps θ hn u * (kap θ hn A)⁻¹ * (N0.eps θ hn u)⁻¹) by group]
    exact mul_mem (hkap A) (hM _ (eps_mem_Dsub θ hn u) _ (inv_mem (hkap A)))
  have h1 : N0.eps θ hn 1 ∈ M := by
    have := hcomm t01 2
    have e : xr (linPerm8 t01 2) 2 = 1 := by decide +kernel
    rwa [e] at this
  have h2 : N0.eps θ hn 2 ∈ M := by
    have := hcomm t12 4
    have e : xr (linPerm8 t12 4) 4 = 2 := by decide +kernel
    rwa [e] at this
  have h4 : N0.eps θ hn 4 ∈ M := by
    have := hcomm t21 2
    have e : xr (linPerm8 t21 2) 2 = 4 := by decide +kernel
    rwa [e] at this
  have hE : ∀ v : Fin 8, N0.eps θ hn v ∈ M := by
    have hmul : ∀ a b : Fin 8, N0.eps θ hn a ∈ M → N0.eps θ hn b ∈ M →
        N0.eps θ hn (a ^^^ b) ∈ M := fun a b ha hb => by
      rw [← N0.eps_mul]
      exact mul_mem ha hb
    have h3 := hmul 1 2 h1 h2
    have h5 := hmul 1 4 h1 h4
    have h6 := hmul 2 4 h2 h4
    have h7 := hmul _ 4 h3 h4
    have h0 : N0.eps θ hn 0 ∈ M := by rw [N0.eps_zero]; exact one_mem M
    have key : ∀ v : Fin 8, v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 1 ^^^ 2 ∨ v = 4 ∨ v = 1 ^^^ 4 ∨
        v = 2 ^^^ 4 ∨ v = (1 ^^^ 2) ^^^ 4 := by decide
    intro v
    rcases key v with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
  intro x hx
  obtain ⟨v, A, rfl⟩ := (mem_Dsub_iff θ hn x).1 hx
  exact mul_mem (hE v) (hkap A)

theorem commutator_Dsub : ⁅Dsub θ hn, Dsub θ hn⁆ = Dsub θ hn := by
  refine le_antisymm (commutator_le_self _) ?_
  refine Dsub_le_of_conj θ hn (M := ⁅Dsub θ hn, Dsub θ hn⁆) (fun d hd m hm => ?_) ?_
  ·
    have h := commutator_mem_commutator hd (commutator_le_self _ hm)
    rw [commutatorElement_def] at h
    rw [show d * m * d⁻¹ = d * m * d⁻¹ * m⁻¹ * m by group]
    exact mul_mem h hm
  ·
    have h1 : t01 ∈
        ⁅(⊤ : Subgroup (GL (Fin 3) (ZMod 2))), (⊤ : Subgroup (GL (Fin 3) (ZMod 2)))⁆ := by
      rw [commutator_GL3]; exact mem_top _
    have h2 : (⁅(⊤ : Subgroup (GL (Fin 3) (ZMod 2))),
        (⊤ : Subgroup (GL (Fin 3) (ZMod 2)))⁆).map (kap θ hn) ≤ ⁅Dsub θ hn, Dsub θ hn⁆ := by
      rw [map_commutator]
      exact commutator_mono (map_le_iff_le_comap.2 fun A _ => kap_mem_Dsub θ hn A)
        (map_le_iff_le_comap.2 fun A _ => kap_mem_Dsub θ hn A)
    exact h2 ⟨t01, h1, rfl⟩

theorem card_Dsub : Nat.card (Dsub θ hn) = 1344 := by
  let f : Fin 8 × GL (Fin 3) (ZMod 2) → Dsub θ hn := fun p =>
    ⟨N0.eps θ hn p.1 * kap θ hn p.2, (mem_Dsub_iff θ hn _).2 ⟨p.1, p.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨v, A⟩ ⟨v', A'⟩ h
      obtain ⟨h1, h2⟩ := eq_of_eps_mul_kap θ hn (congrArg Subtype.val h)
      exact Prod.ext h1 h2
    · rintro ⟨x, hx⟩
      obtain ⟨v, A, rfl⟩ := (mem_Dsub_iff θ hn x).1 hx
      exact ⟨(v, A), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 8),
    Fintype.card_fin, FixedCodim.card_GL3]

theorem center_Dsub : center (Dsub θ hn) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨x, hx⟩ hxc
  rw [mem_center_iff] at hxc
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  show x = 1
  obtain ⟨v, A, rfl⟩ := (mem_Dsub_iff θ hn x).1 hx
  have hc : ∀ y ∈ Dsub θ hn, y * (N0.eps θ hn v * kap θ hn A) =
      (N0.eps θ hn v * kap θ hn A) * y := fun y hy =>
    congrArg Subtype.val (hxc ⟨y, hy⟩)
  have hA : A = 1 := by
    apply linPerm8_injective
    rw [map_one]
    refine Equiv.ext fun u => ?_
    have h1 := hc _ (eps_mem_Dsub θ hn u)
    have h2 : N0.eps θ hn v * kap θ hn A * N0.eps θ hn u * (N0.eps θ hn v * kap θ hn A)⁻¹ =
        N0.eps θ hn u := by
      rw [← h1]; group
    have h3 : N0.eps θ hn v * kap θ hn A * N0.eps θ hn u * (N0.eps θ hn v * kap θ hn A)⁻¹ =
        N0.eps θ hn (linPerm8 A u) := by
      calc N0.eps θ hn v * kap θ hn A * N0.eps θ hn u * (N0.eps θ hn v * kap θ hn A)⁻¹
          = N0.eps θ hn v * (kap θ hn A * N0.eps θ hn u * (kap θ hn A)⁻¹) *
              (N0.eps θ hn v)⁻¹ := by group
        _ = N0.eps θ hn v * N0.eps θ hn (linPerm8 A u) * N0.eps θ hn v := by
            rw [kap_conj_eps, N0.eps_inv]
        _ = N0.eps θ hn (linPerm8 A u) := by
            rw [N0.eps_comm θ hn v, mul_assoc, N0.eps_mul_self, mul_one]
    have h4 := N0.eps_injective θ hn (h3.symm.trans h2)
    rw [Perm.one_apply]
    exact h4
  rw [hA, map_one, mul_one] at hc ⊢
  have hv : ∀ B : GL (Fin 3) (ZMod 2), linPerm8 B v = v := by
    intro B
    have h1 := hc _ (kap_mem_Dsub θ hn B)
    apply N0.eps_injective θ hn
    rw [← kap_conj_eps, h1, mul_inv_cancel_right]
  have hv0 : v = 0 := eq_zero_of_linPerm8_fix v (hv t01) (hv t12) (hv t10)
  rw [hv0, N0.eps_zero]

end Dsub

section Config

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} (c : Config G L Q n θ z)

include c in
theorem Dsub_le_cent : Dsub θ c.hn8 ≤ centralizer ({z} : Set G) :=
  (Dsub_le_L θ c.hn8).trans (AltStdCycTwo.le_cent_single c.ot.std c.ot.cyc)

theorem Dsub_le_N0 : Dsub θ c.hn8 ≤ N0 θ c.hn8 z :=
  sup_le ((le_sup_left : E θ c.hn8 ≤ E θ c.hn8 ⊔ zpowers z).trans Subgroup.le_normalizer)
    (by rintro _ ⟨A, rfl⟩; exact kap_mem_N0 c A)

theorem comm_Dsub_of_odd {u : G} (hu : u ∈ centralizer ({z} : Set G)) (hodd : Odd (orderOf u))
    (hE : ∀ e ∈ E θ c.hn8, u * e = e * u) : ∀ d ∈ Dsub θ c.hn8, u * d = d * u := by
  have hn := c.hn8
  have huN : u ∈ normalizer (L : Set G) := AltStdCycTwo.cent_le_normalizer c.ot.std c.ot.cyc hu
  set x : normalizer (L : Set G) := ⟨u, huN⟩ with hx
  set σ := AltStdBal.rho θ c.hn8 x with hσ
  have hσE : ∀ e ∈ eBar c.hn8, σ * (e : Perm (Fin n)) = e * σ := by
    intro e he
    have h1 := AltStdBal.rho_conj θ c.hn8 x e
    have h2 : (⟨(x : G) * (θ.symm e : G) * (x : G)⁻¹,
        (mem_normalizer_iff.mp x.2 _).mp (θ.symm e).2⟩ : L) = θ.symm e := by
      apply Subtype.ext
      show u * (θ.symm e : G) * u⁻¹ = θ.symm e
      rw [hE _ (mem_E_of_mem_eBar θ c.hn8 he), mul_inv_cancel_right]
    rw [h2, MulEquiv.apply_symm_apply] at h1
    rw [← hσ] at h1
    calc σ * (e : Perm (Fin n)) = σ * (e : Perm (Fin n)) * σ⁻¹ * σ := by group
      _ = e * σ := by rw [h1]
  have hsq : ∀ i : Fin n, i.val < 8 → (σ * σ) i = i := by
    intro i hi
    obtain ⟨h1, h2⟩ := apply_of_comm_eBar c.hn8 hσE hi
    obtain ⟨h3, h4⟩ := apply_of_comm_eBar c.hn8 hσE h1
    apply Fin.ext
    rw [Perm.mul_apply, h4, h2, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have hpow : ∀ k : ℕ, ∀ i : Fin n, i.val < 8 → ((σ * σ) ^ k) i = i := by
    intro k
    induction k with
    | zero => intro i _; rfl
    | succ k ih =>
      intro i hi
      rw [pow_succ, Perm.mul_apply, hsq i hi, ih i hi]
  have hfix : ∀ i : Fin n, i.val < 8 → σ i = i := by
    obtain ⟨k, hk⟩ := hodd
    have hxo : x ^ orderOf u = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, OneMemClass.coe_one]
      exact pow_orderOf_eq_one u)
    have hσo : σ ^ (2 * k + 1) = 1 := by
      rw [← hk, hσ, ← map_pow, hxo, map_one]
    have hσ' : (σ * σ) ^ (k + 1) = σ := by
      rw [← pow_two, ← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, hσo,
        one_mul]
    intro i hi
    calc σ i = ((σ * σ) ^ (k + 1)) i := by rw [hσ']
      _ = i := hpow (k + 1) i hi
  have hge : ∀ i : Fin n, 8 ≤ i.val → 8 ≤ (σ i).val := by
    intro i hi
    by_contra hlt
    push Not at hlt
    have := hfix (σ i) hlt
    have h' : i = σ i := σ.injective this.symm
    rw [← h'] at hlt
    omega
  have hσlin : ∀ A : GL (Fin 3) (ZMod 2), σ * linPerm c.hn8 A = linPerm c.hn8 A * σ := by
    intro A
    ext i
    rw [Perm.mul_apply, Perm.mul_apply]
    by_cases hi : i.val < 8
    · have hl : (linPerm c.hn8 A i).val < 8 := by
        rw [val_linPerm_of_lt c.hn8 A hi]
        exact (linPerm8 A ⟨i.val, hi⟩).2
      rw [hfix _ hl, hfix i hi]
    · push Not at hi
      rw [linPerm_of_ge c.hn8 A hi, linPerm_of_ge c.hn8 A (hge i hi)]
  have hkap : ∀ A : GL (Fin 3) (ZMod 2), u * kap θ c.hn8 A = kap θ c.hn8 A * u := by
    intro A
    have h1 := AltStdBal.rho_conj θ c.hn8 x (lin c.hn8 A)
    rw [← hσ, coe_lin, hσlin A, mul_inv_cancel_right] at h1
    have h2 : (⟨(x : G) * (θ.symm (lin c.hn8 A) : G) * (x : G)⁻¹,
        (mem_normalizer_iff.mp x.2 _).mp (θ.symm (lin c.hn8 A)).2⟩ : L) =
        θ.symm (lin c.hn8 A) := by
      apply θ.injective
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext (by rw [← h1, coe_lin])
    have h3 : u * kap θ c.hn8 A * u⁻¹ = kap θ c.hn8 A := congrArg Subtype.val h2
    calc u * kap θ c.hn8 A = u * kap θ c.hn8 A * u⁻¹ * u := by group
      _ = kap θ c.hn8 A * u := by rw [h3]
  intro d hd
  obtain ⟨v, A, rfl⟩ := (mem_Dsub_iff θ c.hn8 d).1 hd
  rw [← mul_assoc, hE _ (N0.eps_mem_E θ c.hn8 v), mul_assoc, hkap A, mul_assoc]

theorem comm_E_of_mem_ocore {o : G} (ho : o ∈ Ocore θ c.hn8 z)
    (hoz : o ∈ centralizer ({z} : Set G)) : ∀ e ∈ E θ c.hn8, o * e = e * o := by
  intro e he
  have hoN : o ∈ N0 θ c.hn8 z := by
    obtain ⟨y, -, rfl⟩ := ho
    exact y.2
  have heN : e ∈ N0 θ c.hn8 z :=
    Subgroup.le_normalizer (mem_sup_left he : e ∈ E θ c.hn8 ⊔ zpowers z)
  have hoL : o ∈ normalizer (L : Set G) := AltStdCycTwo.cent_le_normalizer c.ot.std c.ot.cyc hoz
  have h1 : o * e * o⁻¹ ∈ E θ c.hn8 :=
    mem_E_of_mem_sup c ((mem_normalizer_iff.1 hoN e).1 (mem_sup_left he))
      ((mem_normalizer_iff.1 hoL e).1 (E_le_L c.hn8 he))
  have h2 : o * e * o⁻¹ * e⁻¹ ∈ E θ c.hn8 ⊓ Ocore θ c.hn8 z := by
    refine Subgroup.mem_inf.2 ⟨mul_mem h1 (inv_mem he), ?_⟩
    rw [show o * e * o⁻¹ * e⁻¹ = o * (e * o⁻¹ * e⁻¹) by group]
    exact mul_mem ho (ocore_conj c heN (inv_mem ho))
  have hbot : E θ c.hn8 ⊓ Ocore θ c.hn8 z = ⊥ := by
    apply inf_eq_bot_of_coprime
    rw [card_E, show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left 3 (coprime_card_oddCoreOf _)
  rw [hbot, mem_bot] at h2
  calc o * e = o * e * o⁻¹ * e⁻¹ * (e * o) := by group
    _ = e * o := by rw [h2, one_mul]

theorem Dsub_inf_ocore_cent :
    Dsub θ c.hn8 ⊓ (Ocore θ c.hn8 z ⊓ centralizer ({z} : Set G)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxD : x ∈ Dsub θ c.hn8 := (mem_inf.1 hx).1
  have hxO : x ∈ Ocore θ c.hn8 z := (mem_inf.1 (mem_inf.1 hx).2).1
  have hxz : x ∈ centralizer ({z} : Set G) := (mem_inf.1 (mem_inf.1 hx).2).2
  have hodd : Odd (orderOf x) :=
    (Nat.coprime_two_left.1 (coprime_card_oddCoreOf (N0 θ c.hn8 z))).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ hxO)
  have hc := comm_Dsub_of_odd c hxz hodd (comm_E_of_mem_ocore c hxO hxz)
  have hcen : (⟨x, hxD⟩ : Dsub θ c.hn8) ∈ center (Dsub θ c.hn8) := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2).symm
  rw [center_Dsub, mem_bot] at hcen
  exact mem_bot.2 (congrArg Subtype.val hcen)

variable {T : Subgroup G} (hH : HData θ c.hn8 z T)

include hH in
theorem kap_mem_normalizer_of_sq {A : GL (Fin 3) (ZMod 2)} (hA : A * A = 1) :
    kap θ c.hn8 A ∈ normalizer (T : Set G) := by
  set k := kap θ c.hn8 A with hk
  set O₀ := Ocore θ c.hn8 z with hO₀
  have hT64 : Nat.card T = 64 := hH.n0.card_eq
  have hTO := T_le_normalizer_ocore c hH
  have hOodd : Nat.Coprime 2 (Nat.card O₀) := coprime_card_oddCoreOf _
  have hOodd' : ∀ x ∈ O₀, Odd (orderOf x) := fun x hx =>
    (Nat.coprime_two_left.1 hOodd).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 6) (by rw [hT64]; norm_num)
  have hkN : k ∈ N0 θ c.hn8 z := kap_mem_N0 c A
  set X := conjSub k T with hX
  have hXle : X ≤ T ⊔ O₀ := by
    rintro _ ⟨t, ht, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hH.n0.normal k hkN t ht
  have hXcard : Nat.card X = 64 := by
    rw [hX, conjSub, card_map_of_injective (MulAut.conj k).injective, hT64]
  have hWcard : Nat.card ↥(T ⊔ O₀) = 64 * Nat.card O₀ := by
    rw [sup_comm, card_sup_of_inf_eq_bot hTO (by rw [inf_comm]; exact T_inf_ocore c hH), hT64]
    ring
  set X' := X.subgroupOf (T ⊔ O₀) with hX'
  have hX'card : Nat.card X' = 64 := by
    rw [hX', Nat.card_congr (subgroupOfEquivOfLe hXle).toEquiv, hXcard]
  have hX'2 : IsPGroup 2 X' := IsPGroup.of_card (n := 6) (by rw [hX'card]; norm_num)
  have hidx : ¬ 2 ∣ X'.index := by
    have h1 := Subgroup.card_mul_index X'
    rw [hX'card, hWcard] at h1
    have h2 : X'.index = Nat.card O₀ := Nat.eq_of_mul_eq_mul_left (by norm_num) h1
    rw [h2]
    obtain ⟨m, hm⟩ := Nat.coprime_two_left.1 hOodd
    omega
  obtain ⟨o, ho, hoX⟩ := exists_conj_eq_of_sylow hTO hT2 hOodd (hX'2.toSylow hidx)
  have hXo : X = conjSub o T := by
    rw [← hoX, IsPGroup.toSylow_coe, hX', subgroupOf_map_subtype, inf_of_le_left hXle]
  have hkz : k * z = z * k := N0.comm_z_of_mem_L c (kap_mem_L θ c.hn8 A)
  have hzX : z ∈ normalizer (X : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    rw [hX, mem_conjSub_iff, mem_conjSub_iff]
    have e : k⁻¹ * (z * x * z⁻¹) * k = z * (k⁻¹ * x * k) * z⁻¹ := by
      have hkz' : k⁻¹ * z = z * k⁻¹ := by
        calc k⁻¹ * z = k⁻¹ * (z * k) * k⁻¹ := by group
          _ = k⁻¹ * (k * z) * k⁻¹ := by rw [hkz]
          _ = z * k⁻¹ := by group
      calc k⁻¹ * (z * x * z⁻¹) * k = (k⁻¹ * z) * x * (z⁻¹ * k) := by group
        _ = (z * k⁻¹) * x * (k * z⁻¹) := by
            rw [hkz', show z⁻¹ * k = k * z⁻¹ by
              calc z⁻¹ * k = z⁻¹ * (k * z) * z⁻¹ := by group
                _ = z⁻¹ * (z * k) * z⁻¹ := by rw [hkz]
                _ = k * z⁻¹ := by group]
        _ = z * (k⁻¹ * x * k) * z⁻¹ := by group
    rw [e]
    exact mem_normalizer_iff.1 hH.n0.norm _
  rw [hXo] at hzX
  obtain ⟨c', hc'O, hc'z, hc'T⟩ := exists_cent_conj (z_mul_self c)
    (fun x hx => ocore_conj c (z_mem_N0 c) hx) hOodd' hH.n0.norm ho hzX
  have hc'k : c' * k = k * c' :=
    comm_Dsub_of_odd c (mem_centralizer_singleton_iff.2 hc'z) (hOodd' c' hc'O)
      (comm_E_of_mem_ocore c hc'O (mem_centralizer_singleton_iff.2 hc'z)) k
      (kap_mem_Dsub θ c.hn8 A)
  have hXc : X = conjSub c' T := by rw [hXo, hc'T]
  have hg : c'⁻¹ * k ∈ normalizer (T : Set G) := by
    rw [mem_normalizer_iff]
    intro t
    have e2 : c'⁻¹ * k * t * (c'⁻¹ * k)⁻¹ = c'⁻¹ * (k * t * k⁻¹) * c' := by group
    rw [e2, ← mem_conjSub_iff, ← hXc, hX, mem_conjSub_iff,
      show k⁻¹ * (k * t * k⁻¹) * k = t by group]
  have hk2 : k * k = 1 := by rw [hk, ← map_mul, hA, map_one]
  have hg2 : (c'⁻¹ * k) * (c'⁻¹ * k) = c'⁻¹ * c'⁻¹ := by
    have hc'k' : k * c'⁻¹ = c'⁻¹ * k := by
      calc k * c'⁻¹ = c'⁻¹ * (c' * k) * c'⁻¹ := by group
        _ = c'⁻¹ * (k * c') * c'⁻¹ := by rw [hc'k]
        _ = c'⁻¹ * k := by group
    calc (c'⁻¹ * k) * (c'⁻¹ * k) = c'⁻¹ * (k * c'⁻¹) * k := by group
      _ = c'⁻¹ * (c'⁻¹ * k) * k := by rw [hc'k']
      _ = c'⁻¹ * c'⁻¹ * (k * k) := by group
      _ = c'⁻¹ * c'⁻¹ := by rw [hk2, mul_one]
  have hc2 : c' * c' ∈ normalizer (T : Set G) := by
    have := inv_mem (mul_mem hg hg)
    rwa [hg2, mul_inv_rev, inv_inv] at this
  have hc : c' ∈ normalizer (T : Set G) := by
    obtain ⟨m, hm⟩ := hOodd' c' hc'O
    have h1 : (c' * c') ^ (m + 1) = c' := by
      rw [← pow_two, ← pow_mul, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, ← hm,
        pow_orderOf_eq_one, one_mul]
    rw [← h1]
    exact pow_mem hc2 _
  have : k = c' * (c'⁻¹ * k) := by group
  rw [this]
  exact mul_mem hc hg

include hH in
theorem kap_mem_normalizer (A : GL (Fin 3) (ZMod 2)) :
    kap θ c.hn8 A ∈ normalizer (T : Set G) := by
  have h := eq_top_of_involutions (S := (normalizer (T : Set G)).comap (kap θ c.hn8))
    fun B hB => kap_mem_normalizer_of_sq c hH hB
  have : A ∈ (normalizer (T : Set G)).comap (kap θ c.hn8) := by rw [h]; exact mem_top A
  exact this

include hH in
theorem Dsub_le_normalizer : Dsub θ c.hn8 ≤ normalizer (T : Set G) :=
  sup_le (hH.n0.E_le.trans Subgroup.le_normalizer)
    (by rintro _ ⟨A, rfl⟩; exact kap_mem_normalizer c hH A)

end Config

end CFSG.OddStandard.AltStdSmall4.W49
