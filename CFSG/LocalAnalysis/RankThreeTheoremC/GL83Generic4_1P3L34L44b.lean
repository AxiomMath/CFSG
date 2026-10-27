module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Shadow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

theorem l34l44_normalizer_le_map {Y X : Type} [Group Y] [Finite Y] [Group X] [Finite X]
    {S : Sylow 3 Y} {z : Y} {Γ : Subgroup Y} (hsh : GenericShadow3 3 S z Γ) (f : Y →* X)
    (hf : Function.Surjective f) {L : Subgroup Y} (hker : f.ker ≤ (S : Subgroup Y))
    (hz : f z = 1) (hL : L ⊓ f.ker = ⊥) {R : Subgroup X}
    (hR : R ≤ ((S : Subgroup Y) ⊓ L).map f) (h1 : 1 ≤ CFSG.Open.pRank 3 R) :
    normalizer (R : Set X) ≤ Γ.map f := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHS : R.comap f ≤ (S : Subgroup Y) := by
    intro h hh
    obtain ⟨s, hs, hfs⟩ := hR (Subgroup.mem_comap.mp hh)
    have hk : s⁻¹ * h ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfs, inv_mul_cancel]
    have h2 := (S : Subgroup Y).mul_mem hs.1 (hker hk)
    rwa [mul_inv_cancel_left] at h2
  obtain ⟨r, hrR, hro⟩ := GenericShadow3.exists_orderOf_eq_of_one_le_pRank Nat.prime_three h1
  obtain ⟨t, ht, hft⟩ := hR hrR
  have htH : t ∈ R.comap f := Subgroup.mem_comap.mpr (hft ▸ hrR)
  have hLH : IsPGroup 3 ↥(L ⊓ R.comap f) := S.isPGroup'.to_le (inf_le_right.trans hHS)
  have hne : Nat.card ↥(L ⊓ R.comap f) ≠ 1 := by
    intro hc
    rw [Subgroup.card_eq_one] at hc
    have htLH : t ∈ L ⊓ R.comap f := ⟨ht.2, htH⟩
    rw [hc, mem_bot] at htLH
    rw [htLH, map_one] at hft
    rw [← hft, orderOf_one] at hro
    omega
  obtain ⟨y, hyo⟩ := exists_prime_orderOf_dvd_card' 3 (hLH.card_eq_or_dvd.resolve_left hne)
  have hyo' : orderOf (y : Y) = 3 := by rw [Subgroup.orderOf_coe]; exact hyo
  have hzk : z ∈ f.ker := MonoidHom.mem_ker.mpr hz
  have hyz : (y : Y) ∉ zpowers z := by
    intro hmem
    have hyk : (y : Y) ∈ L ⊓ f.ker := ⟨y.2.1, zpowers_le.mpr hzk hmem⟩
    rw [hL, mem_bot] at hyk
    rw [hyk, orderOf_one] at hyo'
    omega
  have hzH : z ∈ R.comap f := Subgroup.mem_comap.mpr (hz ▸ R.one_mem)
  have h2 : 2 ≤ CFSG.Open.pRank 3 (R.comap f) :=
    (hsh.two_le_pRank_zpowers_sup hyo' hyz).trans
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three
        (sup_le (zpowers_le.mpr hzH) (zpowers_le.mpr y.2.2)))
  have hNH := hsh.normalizer_le _ hHS h2
  intro n hn
  obtain ⟨m, rfl⟩ := hf n
  exact ⟨m, hNH (le_normalizer_comap f (Subgroup.mem_comap.mpr hn)), rfl⟩

theorem l34l44_rankThreeGamma_le_map {Y X : Type} [Group Y] [Finite Y] [Group X] [Finite X]
    {S : Sylow 3 Y} {z : Y} {Γ : Subgroup Y} (hsh : GenericShadow3 3 S z Γ) (f : Y →* X)
    (hf : Function.Surjective f) {L : Subgroup Y} (hker : f.ker ≤ (S : Subgroup Y))
    (hz : f z = 1) (hL : L ⊓ f.ker = ⊥) {T : Subgroup X}
    (hT : T ≤ ((S : Subgroup Y) ⊓ L).map f) : rankThreeGamma 1 3 T ≤ Γ.map f := by
  refine sSup_le ?_
  rintro N ⟨R, hRT, hR1, rfl⟩
  exact l34l44_normalizer_le_map hsh f hf hker hz hL (hRT.trans hT) hR1

theorem l34l44_le_normalizer_of_not_le {X : Type} [Group X] [Finite X] (hK2 : KFactL34Three)
    {K T W : Subgroup X} (hKn : K.Normal) (hL : IsRankThreeL34 ↥K) (hT : IsElemAbelian 3 T)
    (hTc : Nat.card T = 3 ^ 2) (hTK : T ≤ K) (hTW : T ≤ W)
    (hNW : normalizer (T : Set X) ≤ W) (hKW : ¬ K ≤ W) : W ≤ normalizer (T : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTp : IsPGroup 3 ↥(T.subgroupOf K) := fun g =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hT.2 _ (Subgroup.mem_subgroupOf.mp g.2)))⟩
  obtain ⟨Q, hQ⟩ := hTp.exists_le_sylow
  have hcardT : Nat.card ↥(T.subgroupOf K) = 3 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv, hTc]
  have hQT : (Q : Subgroup K) = T.subgroupOf K :=
    (Subgroup.eq_of_le_of_card_ge hQ (by rw [(hK2 _ hL Q).1, hcardT])).symm
  have hmapQ : (Q : Subgroup K).map K.subtype = T := by
    rw [hQT, Subgroup.map_subgroupOf_eq_of_le hTK]
  have hNQ : normalizer ((Q : Subgroup K) : Set K) ≤ W.subgroupOf K := by
    intro k hk
    have h1 := Subgroup.le_normalizer_map K.subtype ⟨k, hk, rfl⟩
    rw [hmapQ] at h1
    exact Subgroup.mem_subgroupOf.mpr (hNW h1)
  have hWK : W.subgroupOf K = normalizer ((Q : Subgroup K) : Set K) := by
    rcases (hK2 _ hL Q).2.2.1 _ hNQ with h | h
    · exact h
    · refine absurd (fun k hk => ?_) hKW
      have hk' : (⟨k, hk⟩ : K) ∈ W.subgroupOf K := h ▸ mem_top _
      exact Subgroup.mem_subgroupOf.mp hk'
  have hconj : ∀ w ∈ W, ∀ t ∈ T, w * t * w⁻¹ ∈ T := by
    intro w hw t ht
    set k : K := ⟨w * t * w⁻¹, hKn.conj_mem t (hTK ht) w⟩ with hk
    have hkW : k ∈ W.subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr (W.mul_mem (W.mul_mem hw (hTW ht)) (W.inv_mem hw))
    rw [hWK] at hkW
    have hk3 : k ^ 3 = 1 := Subtype.ext (by
      change (w * t * w⁻¹) ^ 3 = 1
      rw [conj_pow, hT.2 t ht, mul_one, mul_inv_cancel])
    have hkp : IsPGroup 3 ↥(zpowers k) := IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hk3)
    have h1 : k ∈ zpowers k ⊓ normalizer ((Q : Subgroup K) : Set K) := ⟨mem_zpowers k, hkW⟩
    have h2 : k ∈ (Q : Subgroup K) := ((hkp.inf_normalizer_sylow Q).le h1).2
    rw [hQT] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  intro w hw
  rw [mem_normalizer_iff]
  intro t
  refine ⟨hconj w hw t, fun h => ?_⟩
  have h1 := hconj w⁻¹ (W.inv_mem hw) _ h
  rwa [inv_inv, show w⁻¹ * (w * t * w⁻¹) * w = t by group] at h1

end CFSG.LocalAnalysis.RankThreeTheoremC
