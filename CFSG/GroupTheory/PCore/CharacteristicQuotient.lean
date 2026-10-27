module

public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal

public section

namespace CFSG

theorem isCharacteristicP_centralizer
    (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hchar : IsCharacteristicP p G) (P : Subgroup G) (hP : IsPGroup p P) :
    IsCharacteristicP p (Subgroup.centralizer (P : Set G)) := by
  have hopen : Subgroup.centralizer (Open.pCore p G : Set G) ≤ Open.pCore p G := by
    exact (show Subgroup.centralizer (pCore p G : Set G) ≤ pCore p G from hchar)
  have hlocal := RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_centralizer
    p Fact.out hopen P hP
  change Subgroup.centralizer
      (pCore p (Subgroup.centralizer (P : Set G)) : Set (Subgroup.centralizer (P : Set G))) ≤
    pCore p (Subgroup.centralizer (P : Set G))
  exact hlocal

theorem pPrimeCore_centralizer_eq_of_isCharacteristicP_quotient
    (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hcop : Nat.Coprime p (Nat.card N))
    (hchar : IsCharacteristicP p (G ⧸ N)) (P : Subgroup G) (hP : IsPGroup p P) :
    (pPrimeCore p (Subgroup.centralizer (P : Set G))).map
        (Subgroup.centralizer (P : Set G)).subtype =
      N ⊓ Subgroup.centralizer (P : Set G) := by
  let C := Subgroup.centralizer (P : Set G)
  let q := QuotientGroup.mk' N
  let : Fact (IsPGroup p P) := ⟨hP⟩
  have himage : Subgroup.centralizer (P.map q : Set (G ⧸ N)) = C.map q :=
    centralizer_map_quotient_eq_map_centralizer p P N inferInstance hcop
  have hcharImage : IsCharacteristicP p (C.map q) := by
    rw [← himage]
    exact isCharacteristicP_centralizer (G ⧸ N) p hchar (P.map q) (hP.map q)
  have hcoreImage : pPrimeCore p (C.map q) = ⊥ :=
    pPrimeCore_eq_bot_of_isCharacteristicP (C.map q) p hcharImage
  let f : C →* C.map q := (q.comp C.subtype).codRestrict (C.map q)
    (fun c => Subgroup.mem_map_of_mem q c.property)
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨c, hc⟩, Subtype.ext hcx⟩
  let : (pPrimeCore p C).Normal := pPrimeCore_normal
  have hmapNormal : ((pPrimeCore p C).map f).Normal :=
    (inferInstance : (pPrimeCore p C).Normal).map f hsurj
  have hmapCoprime : Nat.Coprime p (Nat.card ((pPrimeCore p C).map f)) :=
    (pPrimeCore_coprime_card (p := p) (G := C)).of_dvd_right
      ((pPrimeCore p C).card_map_dvd f)
  have hmapBot : (pPrimeCore p C).map f = ⊥ := by
    apply le_bot_iff.mp
    calc
      (pPrimeCore p C).map f ≤ pPrimeCore p (C.map q) :=
        le_sSup ⟨hmapNormal, hmapCoprime⟩
      _ = ⊥ := hcoreImage
  apply le_antisymm
  · rintro x ⟨c, hc, rfl⟩
    have hfc : f c = 1 := Subgroup.mem_bot.mp
      (hmapBot ▸ Subgroup.mem_map_of_mem f hc)
    have hq : q c.val = 1 := congrArg Subtype.val hfc
    have hkernel : c.val ∈ q.ker := hq
    rw [QuotientGroup.ker_mk'] at hkernel
    exact ⟨hkernel, c.property⟩
  · have hnormal : (N.subgroupOf C).Normal := by infer_instance
    have hcopInternal : Nat.Coprime p (Nat.card (N.subgroupOf C)) := by
      have heq : N.subgroupOf C = (N ⊓ C).subgroupOf C := by
        ext c
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, c.property, and_true]
      rw [heq, Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ C ≤ C)).toEquiv]
      exact hcop.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
    have hle : N.subgroupOf C ≤ pPrimeCore p C := le_sSup ⟨hnormal, hcopInternal⟩
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, hle hx.1, rfl⟩

end CFSG
