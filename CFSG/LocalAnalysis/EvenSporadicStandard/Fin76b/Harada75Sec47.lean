module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75L3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75L22
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Sec46
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Sec47a
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Sec47b
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Sec47c

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section Sec47

variable {S : Type} [Group S] [Finite S]

theorem sec47_final (hS : IsPGroup 2 S) {A E : Subgroup S} [hEn : E.Normal]
    (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8) (hCA : Subgroup.centralizer (A : Set S) ≤ A)
    (hE : IsElemAbelian 2 E) (hE8 : Nat.card E = 8) (hAE4 : Nat.card (A ⊓ E : Subgroup S) = 4)
    (hN : Nat.card (Subgroup.normalizer (A : Set S)) ≤ 32) : GenLE4 S := by
  classical
  by_contra hno
  have hAsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← pow_two]; exact hA.2 x hx
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨a, haA, haE⟩ : ∃ a ∈ A, a ∉ E := by
    by_contra h
    have h' : ∀ a ∈ A, a ∈ E := fun a ha => by
      by_contra hn
      exact h ⟨a, ha, hn⟩
    have hle : A ≤ A ⊓ E := fun x hx => ⟨hx, h' x hx⟩
    have := Subgroup.card_le_of_le hle
    omega
  have ha2 : a * a = 1 := hAsq a haA
  set π := QuotientGroup.mk' E with hπ
  have hPp : IsPGroup 2 (S ⧸ E) := hS.to_quotient E
  have hā1 : (a : S ⧸ E) ≠ 1 := fun h => haE ((QuotientGroup.eq_one_iff a).mp h)
  have hā2 : (a : S ⧸ E) ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul, ha2, QuotientGroup.mk_one]
  have hC4 := card_centralizer_quot_le_four hA hA8 hE hE8 hAE4 hCA hN haA haE
  obtain ⟨Cb, hCbcyc, hCbidx⟩ := exists_cyclic_index_le_two hPp hā2 hā1 hC4
  have hP2 : ∀ U : Subgroup (S ⧸ E), Group.rank U ≤ 2 := fun U =>
    rank_le_two_of_cyclic_index_le_two hCbcyc hCbidx U
  obtain ⟨T, hT⟩ : ∃ T : Subgroup S, 4 < Group.rank T := by
    by_contra h
    have h' : ∀ U : Subgroup S, Group.rank U ≤ 4 := fun U => by
      by_contra hn
      exact h ⟨U, not_le.mp hn⟩
    exact hno (genLE4_of_rank_le_four h')
  obtain ⟨hET, hEphi, hTnc⟩ := sec47_E_le hS hE8 hP2 T hT
  have hSP : Nat.card S = Nat.card E * Nat.card (S ⧸ E) := by
    rw [← Subgroup.index_eq_card]
    exact (Subgroup.card_mul_index E).symm
  have hPcard : Nat.card S = 8 * Nat.card (S ⧸ E) := by rw [hSP, hE8]
  set Tb : Subgroup (S ⧸ E) := T.map π with hTb
  have hTb3 : 3 ≤ Nat.card Tb := by
    by_contra hlt
    exact hTnc (isCyclic_of_natCard_le_two (show Nat.card Tb ≤ 2 by omega))
  have hTbP : Nat.card Tb ≤ Nat.card (S ⧸ E) := Subgroup.card_le_card_group Tb
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hPp
  obtain ⟨m', hm'⟩ := (IsPGroup.iff_card).mp (hPp.to_subgroup Tb)
  have hTb4 : 4 ≤ Nat.card Tb := by
    by_contra hlt
    have hm'1 : m' ≤ 1 := by
      by_contra hm2
      have : 2 ^ 2 ≤ 2 ^ m' := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : 2 ^ m' ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm'1
    omega
  rcases le_or_gt (Nat.card (S ⧸ E)) 4 with hP4 | hP8
  ·
    have hTbtop : Tb = ⊤ := Subgroup.eq_top_of_card_eq Tb (by omega)
    have hTtop : T = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have hg : π g ∈ Tb := by rw [hTbtop]; exact Subgroup.mem_top _
      obtain ⟨t, htT, hgt⟩ := Subgroup.mem_map.mp hg
      have hk : t⁻¹ * g ∈ E := by
        have : π (t⁻¹ * g) = 1 := by rw [map_mul, map_inv, hgt, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff (N := E) _).mp this
      have : g = t * (t⁻¹ * g) := by group
      rw [this]
      exact T.mul_mem htT (hET hk)
    have hTcard : Nat.card T = 32 := by
      rw [hTtop, Subgroup.card_top]
      omega
    have hΦ : Nat.card (phi T) < 2 := by
      by_contra hge
      have hge := not_lt.mp hge
      have h1 : Nat.card T ≤ 2 ^ 4 * Nat.card (phi T) := by
        rw [hTcard]
        omega
      exact absurd (rank_le_of_card_le_mul_phi hS T 4 h1) (not_le.mpr hT)
    have hΦbot : phi T = ⊥ := by
      apply (Subgroup.eq_bot_iff_card _).mpr
      have hpos : 0 < Nat.card (phi T) := Nat.card_pos
      omega
    have hcomm : ∀ x y : S, x * y = y * x := by
      intro x y
      have hx : x ∈ T := by rw [hTtop]; exact Subgroup.mem_top _
      have hy : y ∈ T := by rw [hTtop]; exact Subgroup.mem_top _
      have h2 := comm_mem_phi hS hx hy
      rw [hΦbot, Subgroup.mem_bot] at h2
      calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = y * x := by rw [h2, one_mul]
    have hSA : ∀ g : S, g ∈ A := by
      intro g
      apply hCA
      rw [Subgroup.mem_centralizer_iff]
      intro x _
      exact hcomm x g
    have hle : Nat.card S ≤ Nat.card A := by
      have : (Subgroup.centralizer (A : Set S)) = ⊤ := by
        rw [eq_top_iff]
        intro g _
        rw [Subgroup.mem_centralizer_iff]
        intro x _
        exact hcomm x g
      have h3 : (⊤ : Subgroup S) ≤ A := fun g _ => hSA g
      have := Subgroup.card_le_of_le h3
      rwa [Subgroup.card_top] at this
    omega
  ·
    have hP8' : 8 ≤ Nat.card (S ⧸ E) := by
      by_contra hlt
      have hm3 : m ≤ 2 := by
        by_contra hm2
        have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm3
      omega
    have hCbcard : 4 ≤ Nat.card Cb := by
      have h1 := Subgroup.card_mul_index Cb
      have h2 : Nat.card Cb * 2 ≥ Nat.card (S ⧸ E) := by
        calc Nat.card (S ⧸ E) = Nat.card Cb * Cb.index := h1.symm
          _ ≤ Nat.card Cb * 2 := Nat.mul_le_mul_left _ hCbidx
      omega
    have hCbn : Cb.Normal := normal_of_index_le_two hCbidx
    obtain ⟨m'', hm''⟩ := (IsPGroup.iff_card).mp (hPp.to_subgroup Cb)
    have h2dvd : 2 ∣ Nat.card Cb := by
      rw [hm'']
      have : 2 ≤ m'' := by
        by_contra hlt
        have : m'' ≤ 1 := by omega
        have : 2 ^ m'' ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
        omega
      exact dvd_pow_self 2 (by omega)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    set c : S ⧸ E := (x : S ⧸ E) with hc
    have hcCb : c ∈ Cb := x.2
    have hc2 : c ^ 2 = 1 := by
      have : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
      exact congrArg Subtype.val this
    have hc1 : c ≠ 1 := by
      intro h
      have : x = 1 := Subtype.ext h
      rw [this, orderOf_one] at hx2
      omega
    have hcen : c ∈ Subgroup.center (S ⧸ E) :=
      mem_center_of_involution_mem_cyclic_normal hCbcyc hcCb hc2 hc1
    have hcT : c ∈ Tb :=
      mem_of_not_isCyclic_of_cyclic_index_le_two hPp hCbcyc hCbidx hcCb hc2 hc1 Tb hTnc
    set K₀ : Subgroup S := (Subgroup.zpowers c).comap π with hK₀
    have hzc : Subgroup.zpowers c ≤ Subgroup.center (S ⧸ E) := (Subgroup.zpowers_le).mpr hcen
    have hzn : (Subgroup.zpowers c).Normal := ⟨fun y hy g => by
      have := (Subgroup.mem_center_iff.mp (hzc hy)) g
      rw [this, mul_inv_cancel_right]
      exact hy⟩
    have hK₀n : K₀.Normal := Subgroup.Normal.comap hzn π
    have hEK₀ : E ≤ K₀ := by
      intro e he
      show π e ∈ Subgroup.zpowers c
      have : π e = 1 := (QuotientGroup.eq_one_iff (N := E) e).mpr he
      rw [this]
      exact Subgroup.one_mem _
    have hK₀T : K₀ ≤ T := by
      intro y hy
      have hy' : π y ∈ Subgroup.zpowers c := hy
      have hyTb : π y ∈ Tb := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy'
        rw [← hn]
        exact Tb.zpow_mem hcT n
      obtain ⟨t, htT, hty⟩ := Subgroup.mem_map.mp hyTb
      have hk : t⁻¹ * y ∈ E := by
        have : π (t⁻¹ * y) = 1 := by rw [map_mul, map_inv, hty, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff (N := E) _).mp this
      have : y = t * (t⁻¹ * y) := by group
      rw [this]
      exact T.mul_mem htT (hET hk)
    have hcord : orderOf c = 2 := by
      have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
      have h3 : orderOf c ≠ 1 := fun h => hc1 (orderOf_eq_one_iff.mp h)
      have h4 : 0 < orderOf c := orderOf_pos c
      have h5 := Nat.le_of_dvd (by norm_num) h2
      omega
    have hK16 : Nat.card K₀ = 16 := by
      have h := sec46_card_comap E (Subgroup.zpowers c)
      rw [Nat.card_zpowers, hcord, hE8] at h
      exact h.trans (by norm_num)
    have hK₀E : IsElemAbelian 2 K₀ := sec47_K0 hS hEphi hK₀T hEK₀ hE8 hK16
    have hāc : (a : S ⧸ E) ∉ Subgroup.zpowers c := by
      intro hmem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rcases zpow_eq_one_or_self c (by rw [← pow_two]; exact hc2) n with h1 | h1
      · rw [h1] at hn
        exact hā1 hn.symm
      · rw [h1] at hn
        have hcentTop : Subgroup.centralizer ({(a : S ⧸ E)} : Set (S ⧸ E)) = ⊤ := by
          rw [eq_top_iff]
          intro g _
          rw [Subgroup.mem_centralizer_singleton_iff, ← hn]
          exact Subgroup.mem_center_iff.mp hcen g
        have hcard : Nat.card (Subgroup.centralizer ({(a : S ⧸ E)} : Set (S ⧸ E))) =
            Nat.card (S ⧸ E) := by
          rw [hcentTop, Subgroup.card_top]
        omega
    have haK : a ∉ K₀ := fun h => hāc (show π a ∈ Subgroup.zpowers c from h)
    have hAK : Nat.card (A ⊓ K₀ : Subgroup S) = 4 := by
      have hEq : A ⊓ K₀ = A ⊓ E := by
        apply le_antisymm
        · intro x hx
          refine ⟨hx.1, ?_⟩
          by_contra hxE
          have hi : (E.subgroupOf A).index ≤ 2 := index_subgroupOf_inf_le_two hA8 hAE4
          rcases mem_or_mul_mem_of_subgroupOf_index_le_two hA hi haA haE hx.1 with h | h
          · exact hxE h
          · have h1 : π (x * a) = 1 := (QuotientGroup.eq_one_iff (N := E) _).mpr h
            rw [map_mul] at h1
            have hxK : π x ∈ Subgroup.zpowers c := hx.2
            have h2 : π a = (π x)⁻¹ := eq_inv_of_mul_eq_one_right h1
            exact hāc (by
              show π a ∈ Subgroup.zpowers c
              rw [h2]
              exact Subgroup.inv_mem _ hxK)
        · intro x hx
          exact ⟨hx.1, hEK₀ hx.2⟩
      rw [hEq]
      exact hAE4
    obtain ⟨hZ4, hCZ⟩ := centralizer_Z_le hS hK₀n hK₀E hK16 hA hA8 hCA haA haK hAK
    have hEK₀' : E ≤ K₀.comap (MonoidHom.id S) := by simpa using hEK₀
    set ψ := QuotientGroup.map E K₀ (MonoidHom.id S) hEK₀' with hψ
    have hψsurj : Function.Surjective ψ := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨(g : S ⧸ E), by simp [hψ]⟩
    refine hno (genLE4_of_E16 (F := K₀) hS hK₀E hK16 ha2 hZ4 hCZ ⟨Cb.map ψ, ?_, ?_⟩)
    · have := hCbcyc
      exact isCyclic_of_surjective (ψ.subgroupMap Cb) (ψ.subgroupMap_surjective Cb)
    · have h1 := Subgroup.index_map_dvd hψsurj (H := Cb)
      have hpos : 0 < Cb.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      exact (Nat.le_of_dvd hpos h1).trans hCbidx

end Sec47

end CFSG.EvenSporadicStandard.Fin76b
