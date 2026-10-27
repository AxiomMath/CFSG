module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.CharacterTheory.Semidihedral.CentralHall

public section

namespace CFSG

variable {G H : Type*} [Group G] [Group H] {p : ℕ} [Finite G] [Finite H] [Fact p.Prime]

omit [Finite H] in
theorem map_pPrimeCore_le (f : G →* H) (hf : Function.Surjective f) :
    (pPrimeCore p G).map f ≤ pPrimeCore p H := by
  have hn : ((pPrimeCore p G).map f).Normal := (pPrimeCore_normal (p := p) (G := G)).map f hf
  have hcop : Nat.Coprime p (Nat.card ((pPrimeCore p G).map f)) :=
    Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_surjective (f.subgroupMap_surjective _)) pPrimeCore_coprime_card
  exact le_sSup ⟨hn, hcop⟩

theorem prime_complement_kernel_core_preimage (f : G →* H) (hf : Function.Surjective f)
    (hker : ¬ p ∣ Nat.card f.ker) :
    (pPrimeCore p H).comap f = pPrimeCore p G ∧ (pPrimeCore p G).map f = pPrimeCore p H := by
  have hp : p.Prime := Fact.out
  have hle : pPrimeCore p G ≤ (pPrimeCore p H).comap f :=
    Subgroup.map_le_iff_le_comap.1 (map_pPrimeCore_le f hf)
  have hge : (pPrimeCore p H).comap f ≤ pPrimeCore p G := by
    have hn : ((pPrimeCore p H).comap f).Normal := (pPrimeCore_normal (p := p) (G := H)).comap f
    let g := f.domRestrict ((pPrimeCore p H).comap f)
    have hcard := Subgroup.card_ker_mul_card_range g
    have hrange : Nat.card g.range ∣ Nat.card (pPrimeCore p H) := by
      apply Subgroup.card_dvd_of_le
      rintro _ ⟨v, rfl⟩
      exact v.2
    have hkerdvd : Nat.card g.ker ∣ Nat.card f.ker := by
      have hsub : g.ker.map ((pPrimeCore p H).comap f).subtype ≤ f.ker := by
        rintro _ ⟨v, hv, rfl⟩
        exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hv)
      rw [← Subgroup.card_map_of_injective (K := g.ker)
        ((pPrimeCore p H).comap f).subtype_injective]
      exact Subgroup.card_dvd_of_le hsub
    have hcop : Nat.Coprime p (Nat.card ((pPrimeCore p H).comap f)) := by
      rw [← hcard]
      refine Nat.Coprime.mul_right ?_ ?_
      · exact (hp.coprime_iff_not_dvd.2 hker).coprime_dvd_right hkerdvd
      · exact Nat.Coprime.coprime_dvd_right hrange pPrimeCore_coprime_card
    exact le_sSup ⟨hn, hcop⟩
  have heq := le_antisymm hge hle
  refine ⟨heq, ?_⟩
  rw [← heq, Subgroup.map_comap_eq_self_of_surjective hf]

theorem central_p_kernel_prime_core_image (f : G →* H) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center G) (hpker : IsPGroup p f.ker) :
    pPrimeCore p H = (pPrimeCore p G).map f := by
  refine le_antisymm ?_ (map_pPrimeCore_le f hf)
  let V := (pPrimeCore p H).comap f
  have hVn : V.Normal := (pPrimeCore_normal (p := p) (G := H)).comap f
  have hkV : f.ker ≤ V := fun x hx => by
    change f x ∈ pPrimeCore p H
    rw [MonoidHom.mem_ker.1 hx]
    exact one_mem _
  let A : Subgroup V := f.ker.subgroupOf V
  have hA : A ≤ Subgroup.center V := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hcentral hx) y)
  let g : V →* pPrimeCore p H := (f.domRestrict V).codRestrict _ fun v => v.2
  have hg : Function.Surjective g := by
    rintro ⟨h, hh⟩
    obtain ⟨x, rfl⟩ := hf h
    exact ⟨⟨x, hh⟩, rfl⟩
  have hgker : g.ker = A := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hindex : A.index = Nat.card (pPrimeCore p H) := by
    rw [← hgker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hg, Subgroup.card_top]
  have hAcard : Nat.card A = Nat.card f.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkV).toEquiv
  have hcop : (Nat.card A).Coprime A.index := by
    rw [hindex, hAcard]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpker
    rw [hk]
    exact Nat.Coprime.pow_left k pPrimeCore_coprime_card
  obtain ⟨T, hTchar, hTcard, -, -, -, -, -, -, -, e, he⟩ :=
    Semidihedral.central_hall_subgroup_direct_complement A hA hcop
  have hTn : (T.map V.subtype).Normal := by
    have := hVn
    have := hTchar
    infer_instance
  have hTcop : Nat.Coprime p (Nat.card (T.map V.subtype)) := by
    rw [Subgroup.card_map_of_injective V.subtype_injective, hTcard, hindex]
    exact pPrimeCore_coprime_card
  have hTle : T.map V.subtype ≤ pPrimeCore p G := le_sSup ⟨hTn, hTcop⟩
  intro h hh
  obtain ⟨x, rfl⟩ := hf h
  have hxV : x ∈ V := hh
  obtain ⟨⟨a, t⟩, hat⟩ := e.surjective ⟨x, hxV⟩
  have hx : x = (a : G) * (t : G) := by
    have := congrArg Subtype.val ((he a t).symm.trans hat)
    exact this.symm
  have ha : f (a : G) = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_subgroupOf.1 a.2)
  refine ⟨(t : G), hTle ⟨t, t.2, rfl⟩, ?_⟩
  rw [hx, map_mul, ha, one_mul]

theorem central_p_subgroup_prime_core_quotient (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) (hpZ : IsPGroup p Z) :
    pPrimeCore p (G ⧸ Z) = (pPrimeCore p G).map (QuotientGroup.mk' Z) := by
  apply central_p_kernel_prime_core_image _ (QuotientGroup.mk'_surjective Z)
  · rw [QuotientGroup.ker_mk']
    exact hZ
  · rw [QuotientGroup.ker_mk']
    exact hpZ

end CFSG
