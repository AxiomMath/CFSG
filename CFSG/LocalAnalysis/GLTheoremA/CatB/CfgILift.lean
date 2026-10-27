module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA

section Lift

variable {H : Type} [Group H]

theorem isElemAbelian_map_of_injective {p : ℕ} {K : Type} [Group K] {f : H →* K}
    (hf : Function.Injective f) {S : Subgroup H} (hS : IsElemAbelian p S) :
    IsElemAbelian p (S.map f) := by
  obtain ⟨hc, he⟩ := hS
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · rcases a with ⟨_, a, ha, rfl⟩
    rcases b with ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    have h := congrArg (fun z : S => f (z : H)) (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    simp only [Subgroup.coe_mul, map_mul] at h ⊢
    exact h
  · rintro x ⟨s, hs, rfl⟩
    rw [← map_pow, he s hs, map_one]

theorem inf_eq_bot_of_isElemAbelian {p : ℕ} [Fact p.Prime] {S N : Subgroup H}
    (hS : IsElemAbelian p S) (hN : ¬ p ∣ Nat.card N) : S ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxS, hxN⟩
  have hxp : x ^ p = 1 := hS.2 x hxS
  have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  have h2 : orderOf x ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ h2) hN

theorem card_inf_center_le [Finite H] {N S : Subgroup H} [N.Normal] {E : Subgroup (H ⧸ N)}
    (hSE : S ≤ E.comap (QuotientGroup.mk' N)) (hSN : S ⊓ N = ⊥) :
    Nat.card (S ⊓ Subgroup.center H : Subgroup H) ≤
      Nat.card (E ⊓ Subgroup.center (H ⧸ N) : Subgroup (H ⧸ N)) := by
  classical
  let f : (S ⊓ Subgroup.center H : Subgroup H) → (E ⊓ Subgroup.center (H ⧸ N) : Subgroup (H ⧸ N)) :=
    fun x => ⟨QuotientGroup.mk' N x.1, by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact hSE (Subgroup.mem_inf.1 x.2).1
      · rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
        have hz : x.1 ∈ Subgroup.center H := (Subgroup.mem_inf.1 x.2).2
        rw [Subgroup.mem_center_iff] at hz
        simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hz y]⟩
  apply Nat.card_le_card_of_injective f
  intro x y hxy
  have hxy' : QuotientGroup.mk' N x.1 = QuotientGroup.mk' N y.1 := congrArg Subtype.val hxy
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy'
  have hmem : x.1⁻¹ * y.1 ∈ S ⊓ N := by
    refine Subgroup.mem_inf.2 ⟨S.mul_mem (S.inv_mem (Subgroup.mem_inf.1 x.2).1) (Subgroup.mem_inf.1 y.2).1, ?_⟩
    exact hxy'
  rw [hSN, Subgroup.mem_bot] at hmem
  exact Subtype.ext (inv_mul_eq_one.1 hmem)

end Lift

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_cfgI_lift {p : ℕ} [hp : Fact p.Prime] {I : Subgroup G} {k : ℕ}
    (Ebar : Subgroup (PQuot p I)) (hE : IsElemAbelian p Ebar)
    (hb : p ^ k * Nat.card (Ebar ⊓ Subgroup.center (PQuot p I) : Subgroup (PQuot p I)) ≤
      Nat.card Ebar) :
    ∃ E : Subgroup G, E ≤ I ∧ IsElemAbelian p E ∧
      p ^ k * Nat.card (E ⊓ S8.centerOf I : Subgroup G) ≤ Nat.card E := by
  classical
  have hcop : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥I) := by
    have hc : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥I)) := CFSG.pPrimeCore_coprime_card
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hc
  obtain ⟨S, hSE, hS, hSc⟩ :=
    CFSG.RankThree.Classical2.exists_elemAbelian_lift (GLAPPrimeCore p ↥I) hcop hE
  have hSN : S ⊓ GLAPPrimeCore p ↥I = ⊥ := inf_eq_bot_of_isElemAbelian hS hcop
  have hinj : Function.Injective (I.subtype) := Subtype.val_injective
  refine ⟨S.map I.subtype, Subgroup.map_subtype_le S,
    isElemAbelian_map_of_injective hinj hS, ?_⟩
  have hcen : (S.map I.subtype) ⊓ S8.centerOf I = (S ⊓ Subgroup.center ↥I).map I.subtype := by
    unfold S8.centerOf
    rw [Subgroup.map_inf_eq _ _ _ hinj]
  rw [hcen, Subgroup.card_map_of_injective hinj, Subgroup.card_map_of_injective hinj]
  have hle := card_inf_center_le hSE hSN
  have hSc' : Nat.card S = Nat.card Ebar := hSc
  calc p ^ k * Nat.card (S ⊓ Subgroup.center ↥I : Subgroup ↥I)
      ≤ p ^ k * Nat.card (Ebar ⊓ Subgroup.center (PQuot p I) : Subgroup (PQuot p I)) :=
        Nat.mul_le_mul_left _ hle
    _ ≤ Nat.card Ebar := hb
    _ = Nat.card S := hSc'.symm

end Main

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI
