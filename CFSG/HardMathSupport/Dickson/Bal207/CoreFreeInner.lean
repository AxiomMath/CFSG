module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeLayer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.HardMathSupport.Timmesfeld.CrossChar

section Generic

variable {K : Type*} [Group K] {p : ℕ}

theorem fixSub_conj_eq_centralizer (y : K) :
    fixSub (MulAut.conj y) = Subgroup.centralizer ({y} : Set K) := by
  ext t
  rw [mem_fixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc t * y = (y * t * y⁻¹) * y := by rw [h]
      _ = y * t := by group
  · intro h
    calc y * t * y⁻¹ = (t * y) * y⁻¹ := by rw [h]
      _ = t := by group

theorem coreFreeAt_conj_of_inner (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {y : K} (hA : NoNormalPPrime p (Subgroup.centralizer ({y} : Set K)))
    (hB : ∀ g : MulAut K, Nat.Coprime p (orderOf g) → g y = y →
      (∀ t ∈ Subgroup.centralizer ({y} : Set K), g t = t) → g = 1) :
    CoreFreeAt p (MulAut.conj y) := by
  rw [CoreFreeAt, fixSub_conj_eq_centralizer]
  exact ⟨hA, fun g hg hgy hfix => hB g hg (mem_fixSub_of_commute hinj hgy) hfix⟩

theorem noNormalPPrime_of_isQuasisimple (hp : p.Prime) {J : Subgroup K}
    (hJ : CFSG.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card J)
    (hZ : ∀ z ∈ J, (∀ t ∈ J, z * t = t * z) → Nat.Coprime p (orderOf z) → z = 1) :
    NoNormalPPrime p J := by
  intro N hNJ hNn hNc
  have hN' : (N.subgroupOf J).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.2 (hNn g g.2 n (Subgroup.mem_subgroupOf.1 hn))⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hJ hN' with h | h
  · exfalso
    have hJN : J ≤ N := fun j hj => by
      have hmem : (⟨j, hj⟩ : J) ∈ N.subgroupOf J := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 hmem
    exact hp.ne_one (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hJN) hNc) hpJ)
  · refine eq_bot_iff.2 fun n hn => Subgroup.mem_bot.2 ?_
    have hc := h (Subgroup.mem_subgroupOf.2 hn : (⟨n, hNJ hn⟩ : J) ∈ N.subgroupOf J)
    refine hZ n (hNJ hn) (fun t ht => ?_)
      (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard N hn) hNc)
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨t, ht⟩)).symm

theorem noNormalPPrime_of_components {L : Subgroup K} {ι : Sort*} (J : ι → Subgroup K)
    (hJL : ∀ i, J i ≤ L) (hJn : ∀ i, ∀ f ∈ L, ∀ n ∈ J i, f * n * f⁻¹ ∈ J i)
    (hJ : ∀ i, NoNormalPPrime p (J i))
    (hC : ∀ r ∈ L, (∀ i, ∀ j ∈ J i, r * j = j * r) → Nat.Coprime p (orderOf r) → r = 1) :
    NoNormalPPrime p L := by
  intro R hRL hRn hRc
  refine eq_bot_iff.2 fun r hr => Subgroup.mem_bot.2 (hC r (hRL hr) (fun i j hj => ?_)
    (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard R hr) hRc))
  have hbot : R ⊓ J i = ⊥ := by
    refine hJ i (R ⊓ J i) inf_le_right (fun f hf n hn => Subgroup.mem_inf.2
      ⟨hRn f (hJL i hf) n (Subgroup.mem_inf.1 hn).1,
        hJn i f (hJL i hf) n (Subgroup.mem_inf.1 hn).2⟩) ?_
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hRc
  have h1 : r * j * r⁻¹ * j⁻¹ ∈ R ⊓ J i := by
    refine Subgroup.mem_inf.2 ⟨?_, (J i).mul_mem (hJn i r (hRL hr) j hj) ((J i).inv_mem hj)⟩
    have e : r * j * r⁻¹ * j⁻¹ = r * (j * r⁻¹ * j⁻¹) := by group
    rw [e]
    exact R.mul_mem hr (hRn j (hJL i hj) r⁻¹ (R.inv_mem hr))
  rw [hbot, Subgroup.mem_bot] at h1
  calc r * j = (r * j * r⁻¹ * j⁻¹) * (j * r) := by group
    _ = j * r := by rw [h1, one_mul]

end Generic

end CFSG.HardMathSupport.Dickson.Bal207

end
