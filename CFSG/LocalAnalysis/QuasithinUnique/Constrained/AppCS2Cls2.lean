module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Cls
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Tight

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

namespace Two

variable {t x : G} (X : Two T M H S L t x)
include X

theorem im_conj_mem {A : Subgroup G} (hAN : A ≤ normalizer (L : Set G))
    (hinv : ∀ s ∈ S, conjR A s = A) {s : G} (hs : s ∈ s2SI S L) {g : Perm (Fin 5)}
    (hg : g ∈ X.C.P.im A) : X.C.P.pf s * g * (X.C.P.pf s)⁻¹ ∈ X.C.P.im A := by
  obtain ⟨a, ha, rfl⟩ := (X.C.P.mem_im_pf hAN).1 hg
  have hsa : s * a * s⁻¹ ∈ A := by
    have : a ∈ conjR A s := by rw [hinv s hs.1]; exact ha
    exact mem_conjSubgroup_iff.1 this
  rw [← X.C.P.pf_inv hs.2, ← X.C.P.pf_mul hs.2 (hAN ha),
    ← X.C.P.pf_mul ((normalizer (L : Set G)).mul_mem hs.2 (hAN ha))
      ((normalizer (L : Set G)).inv_mem hs.2)]
  exact (X.C.P.mem_im_pf hAN).2 ⟨_, hsa, rfl⟩

theorem im_eq_bot_or {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hinv : ∀ s ∈ S, conjR A s = A) : X.C.P.im A = ⊥ ∨ X.C.P.im A = Estd := by
  have hD := X.C.D
  have hAB := X.le_baum_of_isMax hA
  have hAN : A ≤ normalizer (L : Set G) := fun a ha => X.C.hBN (hAB ha)
  have hAS₁ : A ≤ s2SI S L := fun a ha => ⟨(hAB ha).1, X.C.hBN (hAB ha)⟩
  have hcard : Nat.card ↥(pCoreOf 2 H) ≤ Nat.card A := (X.card_eq_pCoreOf hA).ge
  have htight := hD.offender_tight X.C.P.toPiData hA.2.1 hAS₁ hcard
  have h1 := X.C.P.card_im_mul hAN
  have h2 := X.C.P.card_fix hAN
  have hpos : 0 < Nat.card ↥(A ⊓ centralizer (blockU L : Set G)) := Nat.card_pos
  have h16 : Nat.card (X.C.P.im A) * Nat.card (FixΔ (X.C.P.im A)) = 16 := by
    rw [← h2]
    have h3 := htight
    rw [← h1] at h3
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card (X.C.P.im A) * Nat.card ↥(blockU L ⊓ centralizer (A : Set G)) *
          Nat.card ↥(A ⊓ centralizer (blockU L : Set G))
        = Nat.card (X.C.P.im A) * Nat.card ↥(A ⊓ centralizer (blockU L : Set G)) *
          Nat.card ↥(blockU L ⊓ centralizer (A : Set G)) := by ring
      _ = 16 * Nat.card ↥(A ⊓ centralizer (blockU L : Set G)) := h3
  have hPE : X.C.P.im A ≤ Estd := by
    rw [← X.C.hB]; exact X.C.P.im_mono hAB
  have hPD : X.C.P.im A ≤ Dstd := hPE.trans fun g hg =>
    (mem_Dstd g).2 (Eset_subset_Dset g ((mem_Estd g).1 hg))
  have hsq : ∀ a ∈ X.C.P.im A, a * a = 1 := fun a ha => Eset_sq a ((mem_Estd a).1 (hPE ha))
  have hcm : ∀ a ∈ X.C.P.im A, ∀ b ∈ X.C.P.im A, a * b = b * a := fun a ha b hb =>
    Eset_comm a ((mem_Estd a).1 (hPE ha)) b ((mem_Estd b).1 (hPE hb))
  obtain ⟨s, hs, hsπ⟩ : ∃ s ∈ s2SI S L, X.C.P.pf s = sig0 := by
    have : sig0 ∈ X.C.P.im (s2SI S L) := by rw [X.C.hS]; exact (mem_Dstd _).2 sig0_mem
    exact (X.C.P.mem_im_pf s2SI_le_normalizer).1 this
  rcases classify_P _ hPD hsq hcm h16 with h | h | h | h
  · left
    refine eq_bot_iff.2 fun g hg => ?_
    rw [Subgroup.mem_bot]
    exact (h g).1 hg
  · exfalso
    have hmem : swap (0 : Fin 5) 1 ∈ X.C.P.im A := (h _).2 (Or.inr rfl)
    have := X.im_conj_mem hAN hinv hs hmem
    rw [hsπ, show (sig0 * swap 0 1 * sig0⁻¹) = swap 2 3 from sig0_conj01] at this
    rcases (h _).1 this with h' | h'
    · exact swap23_ne_one h'
    · exact swap23_ne_swap01 h'
  · exfalso
    have hmem : swap (2 : Fin 5) 3 ∈ X.C.P.im A := (h _).2 (Or.inr rfl)
    have := X.im_conj_mem hAN hinv hs hmem
    rw [hsπ, show (sig0 * swap 2 3 * sig0⁻¹) = swap 0 1 from sig0_conj23] at this
    rcases (h _).1 this with h' | h'
    · exact swap01_ne_one h'
    · exact swap01_ne_swap23 h'
  · right
    ext g
    rw [h g, mem_Estd]

theorem eq_pCoreOf_of_im_bot {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hinv : ∀ s ∈ S, conjR A s = A) (hbot : X.C.P.im A = ⊥) : A = pCoreOf 2 H := by
  have hD := X.C.D
  have hAB := X.le_baum_of_isMax hA
  have hAN : A ≤ normalizer (L : Set G) := fun a ha => X.C.hBN (hAB ha)
  have hC₁ : ∀ a ∈ A, ∀ u ∈ blockU L, a * u = u * a := by
    intro a ha u hu
    have h1 : X.C.P.pf a ∈ X.C.P.im A := (X.C.P.mem_im_pf hAN).2 ⟨a, ha, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact (X.C.P.comm_iff (hAN ha) hu).2 (by rw [h1, vact_one])
  have hC₂ : ∀ a ∈ A, ∀ u ∈ blockU2 L t, a * u = u * a := by
    intro a ha u hu
    have hta : t * a * t⁻¹ ∈ A := by
      have : a ∈ conjR A t := by rw [hinv t hD.ht]; exact ha
      exact mem_conjSubgroup_iff.1 this
    have hu' : t * u * t⁻¹ ∈ blockU L := mem_conjSubgroup_iff.1 hu
    have h2 := hC₁ _ hta _ hu'
    have e1 : (t * a * t⁻¹) * (t * u * t⁻¹) = t * (a * u) * t⁻¹ := by group
    have e2 : (t * u * t⁻¹) * (t * a * t⁻¹) = t * (u * a) * t⁻¹ := by group
    rw [e1, e2] at h2
    exact mul_left_cancel (mul_right_cancel h2)
  have hle : A ≤ pCoreOf 2 H := by
    intro a ha
    rw [← hD.campbell_pkg.2.2.2]
    exact Subgroup.mem_inf.2 ⟨hA.1 ha, Subgroup.mem_centralizer_iff.2
      (hD.U0_comm_of (fun b hb => (hC₁ a ha b hb).symm) (fun b hb => (hC₂ a ha b hb).symm))⟩
  exact Subgroup.eq_of_le_of_card_ge hle (X.card_eq_pCoreOf hA).ge

theorem A_comm_V₁ {A : Subgroup G} (hA : IsMaxElemAbelian S A) (hE : X.C.P.im A = Estd) :
    ∀ a ∈ A, ∀ v ∈ conjR (blockU L) x, a * v = v * a := by
  have hD := X.C.D
  have hAB := X.le_baum_of_isMax hA
  have hAN : A ≤ normalizer (L : Set G) := fun a ha => X.C.hBN (hAB ha)
  have hAab : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    B2F.isElemAbelian_comm hA.2.1 ha ha'
  have hAsq : ∀ a ∈ A, a * a = 1 := fun a ha => by
    have := (C5.isElemAbelian_two_iff.mp hA.2.1).2 a ha
    rwa [pow_two] at this
  have hpfE : ∀ a ∈ A, X.C.P.pf a ∈ Eset := fun a ha => by
    have h1 : X.C.P.pf a ∈ X.C.P.im A := (X.C.P.mem_im_pf hAN).2 ⟨a, ha, rfl⟩
    rw [hE] at h1
    exact (mem_Estd _).1 h1
  have hU₁N : ∀ {u : G}, u ∈ blockU L → u ∈ normalizer (L : Set G) := fun hu =>
    Subgroup.le_normalizer (hD.blockU_le_L hu)
  have hinvE : ∀ g ∈ Eset, g⁻¹ = g := fun g hg => inv_eq_of_mul_eq_one_right (Eset_sq g hg)
  have hP01 : swap (0 : Fin 5) 1 ∈ X.C.P.im A := by rw [hE]; exact (mem_Estd _).2 t1_mem_Eset
  have hP23 : swap (2 : Fin 5) 3 ∈ X.C.P.im A := by rw [hE]; exact (mem_Estd _).2 t2_mem_Eset
  obtain ⟨a₀, ha₀, hpf₀⟩ := (X.C.P.mem_im_pf hAN).1 hP01
  obtain ⟨a₁, ha₁, hpf₁⟩ := (X.C.P.mem_im_pf hAN).1 hP23
  obtain ⟨v₀, hv₀, u₀, hu₀, d₀, hd₀, he₀⟩ := X.decomp₁ (hAB ha₀)
  obtain ⟨v₁, hv₁, u₁, hu₁, d₁, hd₁, he₁⟩ := X.decomp₁ (hAB ha₁)
  subst he₀
  subst he₁
  have hpv₀ : X.C.P.pf v₀ = swap 0 1 := by rw [← X.pf_vud hv₀ hu₀ hd₀]; exact hpf₀
  have hpv₁ : X.C.P.pf v₁ = swap 2 3 := by rw [← X.pf_vud hv₁ hu₁ hd₁]; exact hpf₁
  have sq₀ : vact (X.C.P.pf v₀) (X.C.P.bf u₀) = X.C.P.bf u₀ :=
    (X.C.P.comm_iff (X.V₁_le_N hv₀) hu₀).1 (X.sq_cond hv₀ hu₀ hd₀ (hAsq _ ha₀))
  have sq₁ : vact (X.C.P.pf v₁) (X.C.P.bf u₁) = X.C.P.bf u₁ :=
    (X.C.P.comm_iff (X.V₁_le_N hv₁) hu₁).1 (X.sq_cond hv₁ hu₁ hd₁ (hAsq _ ha₁))
  rw [hpv₀] at sq₀
  rw [hpv₁] at sq₁
  have sq₀' : pact (swap 0 1) (X.C.P.bf u₀).1 = (X.C.P.bf u₀).1 := congrArg Subtype.val sq₀
  have sq₁' : pact (swap 2 3) (X.C.P.bf u₁).1 = (X.C.P.bf u₁).1 := congrArg Subtype.val sq₁
  have cm := X.comm_cond hv₀ hv₁ hu₀ hu₁ hd₀ hd₁ (hAab _ ha₀ _ ha₁)
  rw [hpv₀, hpv₁, Equiv.swap_inv, Equiv.swap_inv] at cm
  have cm' : pact (swap 2 3) (X.C.P.bf u₀).1 + (X.C.P.bf u₁).1 =
      pact (swap 0 1) (X.C.P.bf u₁).1 + (X.C.P.bf u₀).1 := congrArg Subtype.val cm
  obtain ⟨hx₀', hy₁'⟩ := E_comm _ _ cm'
  have hx₀E : ∀ σ ∈ Eset, pact σ (X.C.P.bf u₀).1 = (X.C.P.bf u₀).1 := fixE_of _ sq₀' hx₀'
  have hy₁E : ∀ σ ∈ Eset, pact σ (X.C.P.bf u₁).1 = (X.C.P.bf u₁).1 := fixE_of _ hy₁' sq₁'
  intro a ha v hv
  obtain ⟨v', hv', u', hu', d', hd', he⟩ := X.decomp₁ (hAB ha)
  subst he
  have hpfv' : X.C.P.pf v' ∈ Eset := by
    have := hpfE _ ha
    rwa [X.pf_vud hv' hu' hd'] at this
  have hu'N := hU₁N hu'
  have c0 := X.comm_cond hv' hv₀ hu' hu₀ hd' hd₀ (hAab _ ha _ ha₀)
  have c1 := X.comm_cond hv' hv₁ hu' hu₁ hd' hd₁ (hAab _ ha _ ha₁)
  rw [hpv₀, Equiv.swap_inv] at c0
  rw [hpv₁, Equiv.swap_inv] at c1
  have f0 : vact (X.C.P.pf v')⁻¹ (X.C.P.bf u₀) = X.C.P.bf u₀ :=
    Subtype.ext (hx₀E _ (by rw [hinvE _ hpfv']; exact hpfv'))
  have f1 : vact (X.C.P.pf v')⁻¹ (X.C.P.bf u₁) = X.C.P.bf u₁ :=
    Subtype.ext (hy₁E _ (by rw [hinvE _ hpfv']; exact hpfv'))
  rw [f0] at c0
  rw [f1] at c1
  have c0' : pact (swap 0 1) (X.C.P.bf u').1 + (X.C.P.bf u₀).1 =
      (X.C.P.bf u₀).1 + (X.C.P.bf u').1 := congrArg Subtype.val c0
  have c1' : pact (swap 2 3) (X.C.P.bf u').1 + (X.C.P.bf u₁).1 =
      (X.C.P.bf u₁).1 + (X.C.P.bf u').1 := congrArg Subtype.val c1
  have g0 : pact (swap 0 1) (X.C.P.bf u').1 = (X.C.P.bf u').1 := by
    rw [add_comm (X.C.P.bf u₀).1] at c0'
    exact add_right_cancel c0'
  have g1 : pact (swap 2 3) (X.C.P.bf u').1 = (X.C.P.bf u').1 := by
    rw [add_comm (X.C.P.bf u₁).1] at c1'
    exact add_right_cancel c1'
  have hx'E : ∀ σ ∈ Eset, pact σ (X.C.P.bf u').1 = (X.C.P.bf u').1 := fixE_of _ g0 g1
  have hvu' : ∀ w ∈ conjR (blockU L) x, w * u' = u' * w := by
    intro w hw
    have hpw : X.C.P.pf w ∈ Eset := by
      have h1 : X.C.P.pf w ∈ X.C.P.im (conjR (blockU L) x) :=
        (X.C.P.mem_im_pf (X.C.V_le_N X.hx)).2 ⟨w, hw, rfl⟩
      rw [X.hVE] at h1
      exact (mem_Estd _).1 h1
    exact (X.C.P.comm_iff (X.V₁_le_N hw) hu').2 (Subtype.ext (hx'E _ hpw))
  have hvv' : v' * v = v * v' := X.C.V_comm hv' hv
  have hu'v : u' * v = v * u' := (hvu' v hv).symm
  have hd'v : d' * v = v * d' := (X.D₁_comm_V₁ hd' hv).symm
  calc (v' * u' * d') * v = v' * u' * (d' * v) := by group
    _ = v' * u' * (v * d') := by rw [hd'v]
    _ = v' * (u' * v) * d' := by group
    _ = v' * (v * u') * d' := by rw [hu'v]
    _ = (v' * v) * u' * d' := by group
    _ = (v * v') * u' * d' := by rw [hvv']
    _ = v * (v' * u' * d') := by group

end Two

end CFSG.QuasithinUnique.AppCS2
