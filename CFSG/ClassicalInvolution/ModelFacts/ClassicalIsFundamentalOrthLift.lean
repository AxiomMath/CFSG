module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalInvolutions
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSplit

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement

section Hom

variable {K Γ : Type*} [Group K] [Group Γ] (θ : K →* Γ)

theorem commutatorElement_mul_central {a b c d : K} (hc : c ∈ Subgroup.center K)
    (hd : d ∈ Subgroup.center K) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hc' := fun g : K => Subgroup.mem_center_iff.mp hc g
  have hd' := fun g : K => Subgroup.mem_center_iff.mp hd g
  rw [commutatorElement_def, commutatorElement_def]
  calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
      = a * (c * (b * d)) * c⁻¹ * a⁻¹ * (d⁻¹ * b⁻¹) := by group
    _ = a * ((b * d) * c) * c⁻¹ * a⁻¹ * (d⁻¹ * b⁻¹) := by rw [← hc' (b * d)]
    _ = a * (b * d) * a⁻¹ * (d⁻¹ * b⁻¹) := by group
    _ = a * b * (d * a⁻¹) * (d⁻¹ * b⁻¹) := by group
    _ = a * b * (a⁻¹ * d) * (d⁻¹ * b⁻¹) := by rw [← hd' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem eq_of_map_eq_of_isPerfect (hker : θ.ker ≤ Subgroup.center K) {L L' : Subgroup K}
    (hL : ⁅L, L⁆ = L) (hL' : ⁅L', L'⁆ = L') (h : L.map θ = L'.map θ) : L = L' := by
  have key : ∀ {L L' : Subgroup K}, ⁅L', L'⁆ = L' → L.map θ ≤ L'.map θ → ⁅L, L⁆ ≤ L' := by
    intro L L' hL' h
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    obtain ⟨x', hx', hxx'⟩ := h (Subgroup.mem_map_of_mem θ hx)
    obtain ⟨y', hy', hyy'⟩ := h (Subgroup.mem_map_of_mem θ hy)
    have hcx : x'⁻¹ * x ∈ Subgroup.center K := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxx', inv_mul_cancel])
    have hcy : y'⁻¹ * y ∈ Subgroup.center K := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyy', inv_mul_cancel])
    have hx2 : x = x' * (x'⁻¹ * x) := by group
    have hy2 : y = y' * (y'⁻¹ * y) := by group
    rw [hx2, hy2, commutatorElement_mul_central hcx hcy]
    rw [← hL']
    exact Subgroup.commutator_mem_commutator hx' hy'
  refine le_antisymm ?_ ?_
  · calc L = ⁅L, L⁆ := hL.symm
      _ ≤ L' := key hL' h.le
  · calc L' = ⁅L', L'⁆ := hL'.symm
      _ ≤ L := key hL h.ge

theorem commutator_le_map_centralizer (hker : θ.ker ≤ Subgroup.center K) (z : K) :
    ⁅θ.range ⊓ Subgroup.centralizer ({θ z} : Set Γ),
        θ.range ⊓ Subgroup.centralizer ({θ z} : Set Γ)⁆ ≤
      (Subgroup.centralizer ({z} : Set K)).map θ := by
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  obtain ⟨⟨x', rfl⟩, hxc⟩ := hx
  obtain ⟨⟨y', rfl⟩, hyc⟩ := hy
  have hconj : ∀ g : K, θ g ∈ Subgroup.centralizer ({θ z} : Set Γ) →
      g⁻¹ * z * g * z⁻¹ ∈ Subgroup.center K := by
    intro g hg
    refine hker ?_
    have h1 := Subgroup.mem_centralizer_iff.mp hg (θ z) (Set.mem_singleton _)
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc (θ g)⁻¹ * θ z * θ g * (θ z)⁻¹ = (θ g)⁻¹ * (θ z * θ g) * (θ z)⁻¹ := by group
      _ = (θ g)⁻¹ * (θ g * θ z) * (θ z)⁻¹ := by rw [h1]
      _ = 1 := by group
  have hx1 := hconj x' hxc
  have hy1 := hconj y' hyc
  refine ⟨⁅x', y'⁆, ?_, map_commutatorElement θ x' y'⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff.mp hw]
  have hzx : z * x' * z⁻¹ = x' * (x'⁻¹ * z * x' * z⁻¹) := by group
  have hzy : z * y' * z⁻¹ = y' * (y'⁻¹ * z * y' * z⁻¹) := by group
  have hconj_comm : z * ⁅x', y'⁆ * z⁻¹ = ⁅x', y'⁆ := by
    have h := map_commutatorElement (MulAut.conj z).toMonoidHom x' y'
    have e1 : (MulAut.conj z).toMonoidHom ⁅x', y'⁆ = z * ⁅x', y'⁆ * z⁻¹ := rfl
    have e2 : (MulAut.conj z).toMonoidHom x' = z * x' * z⁻¹ := rfl
    have e3 : (MulAut.conj z).toMonoidHom y' = z * y' * z⁻¹ := rfl
    rw [e1, e2, e3, hzx, hzy, commutatorElement_mul_central hx1 hy1] at h
    exact h
  calc z * ⁅x', y'⁆ = (z * ⁅x', y'⁆ * z⁻¹) * z := by group
    _ = ⁅x', y'⁆ * z := by rw [hconj_comm]

theorem le_map_centralizer_of_isPerfect (hker : θ.ker ≤ Subgroup.center K) {O : Subgroup Γ}
    (hrange : θ.range = ⁅O, O⁆) (z : K) {N : Subgroup Γ} (hNO : N ≤ O)
    (hNC : N ≤ Subgroup.centralizer ({θ z} : Set Γ)) (hNp : ⁅N, N⁆ = N) :
    N ≤ (Subgroup.centralizer ({z} : Set K)).map θ := by
  have hNr : N ≤ θ.range := by
    rw [hrange]
    calc N = ⁅N, N⁆ := hNp.symm
      _ ≤ ⁅O, O⁆ := Subgroup.commutator_mono hNO hNO
  calc N = ⁅N, N⁆ := hNp.symm
    _ ≤ ⁅θ.range ⊓ Subgroup.centralizer ({θ z} : Set Γ),
        θ.range ⊓ Subgroup.centralizer ({θ z} : Set Γ)⁆ :=
      Subgroup.commutator_mono (le_inf hNr hNC) (le_inf hNr hNC)
    _ ≤ _ := commutator_le_map_centralizer θ hker z

theorem isSubnormal_inf {A T B : Subgroup K} (h : IsSubnormal A T) (hB : B ≤ T) :
    IsSubnormal (A ⊓ B) B := by
  induction h generalizing B with
  | refl => rw [inf_eq_right.mpr hB]; exact IsSubnormal.refl B
  | @step H M K' hHM hN _ ih =>
    refine IsSubnormal.step (H := H ⊓ B) (M := M ⊓ B) (inf_le_inf_right B hHM) ?_ (ih hB)
    rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right B hHM)]
    intro h k hh hk
    exact ⟨(Subgroup.normal_subgroupOf_iff hHM).mp hN h k hh.1 hk.1,
      B.mul_mem (B.mul_mem hk.2 hh.2) (B.inv_mem hk.2)⟩

theorem isSubnormal_map {A B : Subgroup K} (h : IsSubnormal A B) :
    IsSubnormal (A.map θ) (B.map θ) :=
  h.map θ

end Hom

section PerfectCore

variable {G : Type*} [Group G]

@[expose] def perfectCore (N : Subgroup G) : Subgroup G :=
  ⨆ (S : Subgroup G) (_ : S ≤ N) (_ : ⁅S, S⁆ = S), S

theorem le_perfectCore {N S : Subgroup G} (hS : S ≤ N) (hperf : ⁅S, S⁆ = S) :
    S ≤ perfectCore N :=
  le_iSup_of_le S (le_iSup_of_le hS (le_iSup_of_le hperf le_rfl))

theorem perfectCore_le (N : Subgroup G) : perfectCore N ≤ N :=
  iSup_le fun _ => iSup_le fun hS => iSup_le fun _ => hS

theorem perfectCore_perfect (N : Subgroup G) : ⁅perfectCore N, perfectCore N⁆ = perfectCore N := by
  refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) ?_
  refine iSup_le fun S => iSup_le fun hS => iSup_le fun hperf => ?_
  calc S = ⁅S, S⁆ := hperf.symm
    _ ≤ ⁅perfectCore N, perfectCore N⁆ :=
      Subgroup.commutator_mono (le_perfectCore hS hperf) (le_perfectCore hS hperf)

end PerfectCore

section Classical

variable {p f : ℕ} [Fact p.Prime] {K Γ : Type} [Group K] [Group Γ] (θ : K →* Γ)

theorem inf_ker_eq_bot_of_isClassicalMember [Finite K] (hker : θ.ker ≤ Subgroup.center K)
    (hker2 : ∀ c ∈ θ.ker, c * c = 1) (hodd : Odd (Nat.card (GaloisField p f))) {L : Subgroup K}
    {z : K} (h : IsClassicalMember p f L z) (hz : θ z ≠ 1) : L ⊓ θ.ker = ⊥ := by
  obtain ⟨e⟩ := h.nonempty_equiv
  refine eq_bot_iff.mpr fun c hc => ?_
  rw [Subgroup.mem_bot]
  by_contra hc1
  have hc2 : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hker2 c hc.2) hc1
  have hcz : c ≠ z := fun h' => hz (by rw [← h']; exact hc.2)
  exact false_of_two_commuting_involutions_sl2 hodd e (a := ⟨c, hc.1⟩) (b := ⟨z, h.mem⟩)
    (by rw [Subgroup.orderOf_mk]; exact hc2)
    (by rw [Subgroup.orderOf_mk]; exact h.orderOf_eq_two)
    (Subtype.ext ((Subgroup.mem_center_iff.mp (hker hc.2) z).symm))
    (fun hh => hcz (congrArg Subtype.val hh))

theorem uniqueInvolution_map [Finite K] (hodd : Odd (Nat.card (GaloisField p f)))
    {L : Subgroup K} {z : K} (h : IsClassicalMember p f L z) (hLinf : L ⊓ θ.ker = ⊥) :
    ∀ a ∈ L.map θ, ∀ b ∈ L.map θ, orderOf a = 2 → orderOf b = 2 → a * b = b * a → a = b := by
  obtain ⟨e⟩ := h.nonempty_equiv
  have hinj : ∀ x ∈ L, ∀ y ∈ L, θ x = θ y → x = y := by
    intro x hx y hy hxy
    have hmem : x⁻¹ * y ∈ L ⊓ θ.ker :=
      Subgroup.mem_inf.mpr ⟨L.mul_mem (L.inv_mem hx) hy, MonoidHom.mem_ker.mpr (by
        rw [map_mul, map_inv, hxy, inv_mul_cancel])⟩
    rw [hLinf, Subgroup.mem_bot] at hmem
    exact (inv_mul_eq_one.mp hmem)
  have hord : ∀ x ∈ L, orderOf (θ x) = 2 → orderOf x = 2 := by
    intro x hx h2
    have hsq : (θ x) ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one _
    have hxx : x * x = 1 := by
      have hmem : x * x ∈ L ⊓ θ.ker :=
        Subgroup.mem_inf.mpr ⟨L.mul_mem hx hx, MonoidHom.mem_ker.mpr (by
          rw [map_mul, ← pow_two, hsq])⟩
      rw [hLinf, Subgroup.mem_bot] at hmem
      exact hmem
    have hx1 : x ≠ 1 := fun h1 => by
      rw [h1, map_one, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    exact orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ ha hb hab
  by_contra hne
  have hxy : x ≠ y := fun h' => hne (by rw [h'])
  have hcomm : x * y = y * x :=
    hinj _ (L.mul_mem hx hy) _ (L.mul_mem hy hx) (by rw [map_mul, map_mul]; exact hab)
  exact false_of_two_commuting_involutions_sl2 hodd e (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
    (by rw [Subgroup.orderOf_mk]; exact hord x hx ha)
    (by rw [Subgroup.orderOf_mk]; exact hord y hy hb)
    (Subtype.ext hcomm) (fun hh => hxy (congrArg Subtype.val hh))

theorem false_of_isClassicalMember_of_central [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (hodd : Odd (Nat.card (GaloisField p f))) {L : Subgroup K} {z : K}
    (h : IsClassicalMember p f L z) (hz : z ∈ Subgroup.center K) {y : K} (hy : orderOf y = 2)
    (hyz : y ≠ z) : False := by
  obtain ⟨e⟩ := h.nonempty_equiv
  have hcent : Subgroup.centralizer ({z} : Set K) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    simpa using hz
  have hsub : IsSubnormal L (⊤ : Subgroup K) := by
    have := h.subnormal
    rwa [hcent] at this
  have hq : CFSG.Open.IsQuasisimple (⊤ : Subgroup K) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv Subgroup.topEquiv hK
  rcases eq_or_le_center_of_isSubnormal hsub (native_isQuasisimple hq) with hL | hL
  · have hyL : y ∈ L := by rw [hL]; exact Subgroup.mem_top y
    exact false_of_two_commuting_involutions_sl2 hodd e (a := ⟨y, hyL⟩) (b := ⟨z, h.mem⟩)
      (by rw [Subgroup.orderOf_mk]; exact hy)
      (by rw [Subgroup.orderOf_mk]; exact h.orderOf_eq_two)
      (Subtype.ext ((Subgroup.mem_center_iff.mp hz y)))
      (fun hh => hyz (congrArg Subtype.val hh))
  · apply h.not_le_center
    intro x hx
    obtain ⟨⟨w, hw⟩, hwc, hwx⟩ := hL hx
    rw [← hwx]
    exact (Subgroup.mem_center_iff.mpr fun g => by
      have := Subgroup.mem_center_iff.mp hwc ⟨g, Subgroup.mem_top g⟩
      exact congrArg Subtype.val this)

end Classical

end CFSG.ClassicalInvolution.ModelFacts
