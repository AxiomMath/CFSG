module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {H : Subgroup G}

theorem kSub_le (p : ℕ) (M H : Subgroup G) : kSub p M H ≤ H := by
  unfold kSub
  split_ifs
  · apply sSup_le
    rintro Y ⟨hYH, _⟩
    exact hYH
  · apply sSup_le
    rintro Y ⟨hY, _⟩
    exact hY.1

theorem kSub_of_le (hL : pLayerIn p H ≤ M) :
    kSub p M H = sSup {Y : Subgroup G | Y ≤ H ∧ Nat.card Y = p} := by
  unfold kSub
  rw [if_pos hL]

private theorem kSub_eq_closure_of_le (hp : p.Prime) (hL : pLayerIn p H ≤ M) :
    kSub p M H = closure {x : G | x ∈ H ∧ orderOf x = p} := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [kSub_of_le hL]
  apply le_antisymm
  · apply sSup_le
    rintro Y ⟨hYH, hYcard⟩
    have hYne : Y ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card Y = 1 := by rw [hbot, Subgroup.card_bot]
      rw [hYcard] at h1
      exact hp.ne_one h1
    haveI : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hYne
    obtain ⟨y, hyY, hy1⟩ := Subgroup.exists_ne_one_of_nontrivial Y
    have hyorder : orderOf y = p := by
      apply orderOf_eq_prime
      · exact orderOf_dvd_iff_pow_eq_one.mp
          (by rw [← hYcard]; exact Subgroup.orderOf_dvd_natCard Y hyY)
      · exact hy1
    have hYeq : Subgroup.zpowers y = Y := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyY)
      rw [Nat.card_zpowers, hyorder, hYcard]
    rw [← hYeq]
    exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨hYH hyY, hyorder⟩)
  · rw [Subgroup.closure_le]
    intro x hx
    exact le_sSup
      (show Subgroup.zpowers x ∈ {Y : Subgroup G | Y ≤ H ∧ Nat.card Y = p} from
        ⟨Subgroup.zpowers_le.mpr hx.1, by rw [Nat.card_zpowers, hx.2]⟩)
      (Subgroup.mem_zpowers x)

theorem kSub_normal_of_le (hL : pLayerIn p H ≤ M) : ((kSub p M H).subgroupOf H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (kSub_le p M H)]
  intro h k hh hk
  rw [kSub_of_le hL] at hh ⊢
  have hconj_mem : ∀ Y : Subgroup G, Y ≤ H → Nat.card Y = p →
      Subgroup.map (MulAut.conj k).toMonoidHom Y ≤ H ∧
        Nat.card (Subgroup.map (MulAut.conj k).toMonoidHom Y) = p := by
    intro Y hYH hYcard
    refine ⟨?_, ?_⟩
    · calc Subgroup.map (MulAut.conj k).toMonoidHom Y ≤
            Subgroup.map (MulAut.conj k).toMonoidHom H := Subgroup.map_mono hYH
        _ = H := Subgroup.mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer hk)
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj k).toMonoidHom)
        (MulAut.conj k).injective, hYcard]
  have hmap : Subgroup.map (MulAut.conj k).toMonoidHom
        (sSup {Y : Subgroup G | Y ≤ H ∧ Nat.card Y = p}) ≤
      sSup {Y : Subgroup G | Y ≤ H ∧ Nat.card Y = p} := by
    rw [(Subgroup.gc_map_comap (MulAut.conj k).toMonoidHom).l_sSup]
    refine iSup_le fun Y => iSup_le fun hY => le_sSup (hconj_mem Y hY.1 hY.2)
  have := hmap (Subgroup.mem_map.mpr ⟨h, hh, rfl⟩)
  simpa [MulAut.conj_apply] using this

theorem le_kSub_of_le (hp : p.Prime) (hL : pLayerIn p H ≤ M) {A : Subgroup G} (hAH : A ≤ H)
    (hA : ∀ a ∈ A, a ^ p = 1) : A ≤ kSub p M H := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [kSub_eq_closure_of_le hp hL]
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨hAH ha, orderOf_eq_prime (hA a ha) ha1⟩

theorem kStar_eq_starImg (p : ℕ) (M H : Subgroup G) : kStar p M H = starImg p H (kSub p M H) :=
  rfl

theorem kStar_normal_of_le (hL : pLayerIn p H ≤ M) : (kStar p M H).Normal := by
  exact (kSub_normal_of_le hL).map _ (QuotientGroup.mk'_surjective _)

private theorem closure_subgroupOf_eq (s : Set G) (hs : s ⊆ H) :
    (closure s).subgroupOf H = closure {z : ↥H | (z : G) ∈ s} := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le ((Subgroup.closure_le H).mpr hs), MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, hs hx⟩, hx, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact hz

theorem kStar_eq_closure_of_le (hp : p.Prime) (hL : pLayerIn p H ≤ M) :
    kStar p M H = closure {x : StarGroup p H | orderOf x = p} := by
  haveI : Fact p.Prime := ⟨hp⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let ν : ↥H →* StarGroup p H := QuotientGroup.mk' O
  have hsc : Nat.Coprime p (Nat.card O) := primeComplementCore_coprime p
  let S : Set G := {x : G | x ∈ H ∧ orderOf x = p}
  have hK : kSub p M H = closure S := kSub_eq_closure_of_le hp hL
  apply le_antisymm
  · show ((kSub p M H).subgroupOf H).map ν ≤ closure {x : StarGroup p H | orderOf x = p}
    rw [hK, closure_subgroupOf_eq S (fun x hx => hx.1), MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro y ⟨z, hz, rfl⟩
    have hzord : orderOf z = p := (Subgroup.orderOf_coe z).symm.trans hz.2
    have hdvd : orderOf (ν z) ∣ p := by
      have h := orderOf_map_dvd ν z
      rwa [hzord] at h
    have hne : orderOf (ν z) ≠ 1 := by
      intro h1
      have hz1 : ν z = 1 := orderOf_eq_one_iff.mp h1
      have hzO : z ∈ O := (QuotientGroup.eq_one_iff (N := O) z).mp hz1
      have hdvdO : orderOf z ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hzO
      have hpeq : p = 1 := Nat.eq_one_of_dvd_coprimes hsc (dvd_refl p) (hzord ▸ hdvdO)
      exact hp.ne_one hpeq
    exact orderOf_eq_prime (orderOf_dvd_iff_pow_eq_one.mp hdvd)
      (fun h => hne (orderOf_eq_one_iff.mpr h))
  · rw [Subgroup.closure_le]
    intro x hx
    change x ∈ ((kSub p M H).subgroupOf H).map ν
    rw [hK, closure_subgroupOf_eq S (fun x hx => hx.1), MonoidHom.map_closure]
    obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective O x
    have hxne : x ≠ 1 := by
      intro h
      have h1 : orderOf x = 1 := by rw [h, orderOf_one]
      rw [hx] at h1
      exact hp.ne_one h1
    have hy₀ne : orderOf y₀ ≠ 0 := (orderOf_pos y₀).ne'
    obtain ⟨a, m, hmp, horder⟩ := Nat.exists_eq_pow_mul_and_not_dvd hy₀ne p hp.ne_one
    have hmcop : Nat.Coprime m (orderOf x) := by
      rw [hx]
      exact ((hp.coprime_iff_not_dvd (n := m)).mpr hmp).symm
    obtain ⟨m', hm'⟩ := exists_pow_eq_self_of_coprime (x := x) (n := m) hmcop
    let y : ↥H := y₀ ^ (m * m')
    have hνy : ν y = x := by
      change ν (y₀ ^ (m * m')) = x
      rw [map_pow, hy₀, pow_mul, hm']
    have hy_pow : y ^ (p ^ a) = 1 := by
      have h1 : y₀ ^ (p ^ a * m) = 1 := by rw [← horder, pow_orderOf_eq_one]
      calc y ^ (p ^ a) = (y₀ ^ (m * m')) ^ (p ^ a) := rfl
        _ = y₀ ^ ((m * m') * (p ^ a)) := by rw [← pow_mul]
        _ = y₀ ^ ((p ^ a * m) * m') := by
              rw [show (m * m') * (p ^ a) = (p ^ a * m) * m' by ac_rfl]
        _ = (y₀ ^ (p ^ a * m)) ^ m' := by rw [pow_mul]
        _ = 1 := by rw [h1, one_pow]
    have hyne : y ≠ 1 := by
      intro h
      apply hxne
      rw [← hνy, h, map_one]
    have hνpow : ν (y ^ p) = 1 := by
      rw [map_pow, hνy]
      have hdvd' : orderOf x ∣ p := by rw [hx]
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd'
    have hyO : y ^ p ∈ O := (QuotientGroup.eq_one_iff (N := O) (y ^ p)).mp hνpow
    have hdvd_pow : orderOf (y ^ p) ∣ p ^ a := by
      apply orderOf_dvd_of_pow_eq_one
      calc (y ^ p) ^ (p ^ a) = y ^ (p * p ^ a) := by rw [← pow_mul]
        _ = y ^ (p ^ a * p) := by rw [mul_comm]
        _ = (y ^ (p ^ a)) ^ p := by rw [pow_mul]
        _ = 1 := by rw [hy_pow, one_pow]
    have hdvdO : orderOf (y ^ p) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hyO
    have hk1 : orderOf (y ^ p) = 1 :=
      Nat.eq_one_of_dvd_coprimes (hsc.pow_left a) hdvd_pow hdvdO
    have hypow : y ^ p = 1 := orderOf_eq_one_iff.mp hk1
    have hyorder : orderOf y = p := orderOf_eq_prime hypow hyne
    exact Subgroup.subset_closure (show x ∈ ν '' {z : ↥H | (z : G) ∈ S} from
      ⟨y, ⟨y.2, by rw [Subgroup.orderOf_coe, hyorder]⟩, hνy⟩)

theorem pCore_eq_subgroupOf_pCore {X : Type*} [Group X] [Finite X] [Fact p.Prime]
    (K : Subgroup X) [K.Normal] : CFSG.pCore p ↥K = (CFSG.pCore p X).subgroupOf K := by
  apply le_antisymm
  · rw [← Subgroup.map_le_map_iff_of_injective K.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
    refine le_inf ?_ (Subgroup.map_subtype_le (CFSG.pCore p ↥K))
    apply le_sSup
    exact ⟨inferInstance, (CFSG.pCore_isPGroup (p := p) (G := ↥K)).map K.subtype⟩
  · apply le_sSup
    exact ⟨(CFSG.pCore_normal (p := p) (G := X)).comap K.subtype,
      (CFSG.pCore_isPGroup (p := p) (G := X)).comap_of_injective K.subtype
        K.subtype_injective⟩

theorem nonempty_quot_pCore_mulEquiv_map {X : Type*} [Group X] [Finite X] [Fact p.Prime]
    (K : Subgroup X) [K.Normal] :
    Nonempty (↥K ⧸ CFSG.pCore p ↥K ≃* ↥(K.map (QuotientGroup.mk' (CFSG.pCore p X)))) := by
  let f : ↥K →* X ⧸ CFSG.pCore p X :=
    (QuotientGroup.mk' (CFSG.pCore p X)).comp K.subtype
  have hker : f.ker = CFSG.pCore p ↥K := by
    change ((QuotientGroup.mk' (CFSG.pCore p X)).comp K.subtype).ker = CFSG.pCore p ↥K
    rw [← MonoidHom.comap_ker (QuotientGroup.mk' (CFSG.pCore p X)) K.subtype,
      QuotientGroup.ker_mk', pCore_eq_subgroupOf_pCore]
    rfl
  have hrange : f.range = K.map (QuotientGroup.mk' (CFSG.pCore p X)) := by
    change ((QuotientGroup.mk' (CFSG.pCore p X)).comp K.subtype).range =
      K.map (QuotientGroup.mk' (CFSG.pCore p X))
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivRange f)).trans (MulEquiv.subgroupCongr hrange)⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
