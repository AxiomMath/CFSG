module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJNorm

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem actsAs_pow' {g : G} {α : MulAut (L ⧸ center L)} (h : ActsAs L g α) (n : ℕ) :
    ActsAs L (g ^ n) (α ^ n) := by
  induction n with
  | zero => simpa using actsAs_one L
  | succ n ih => rw [pow_succ, pow_succ]; exact actsAs_mul L ih h

private theorem actsAs_zpow' {g : G} {α : MulAut (L ⧸ center L)} (h : ActsAs L g α) (k : ℤ) :
    ActsAs L (g ^ k) (α ^ k) := by
  rcases lt_or_ge k 0 with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hk
    simpa [zpow_negSucc] using actsAs_inv L (actsAs_pow' h (n + 1))
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simpa [zpow_natCast] using actsAs_pow' h n

private theorem eq_one_of_pow_eq_one_of_odd {x : G} (h2 : IsPGroup 2 ↥(zpowers x)) {M : ℕ}
    (hM : Odd M) (hxM : x ^ M = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp h2 ⟨x, Subgroup.mem_zpowers x⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using hk
  have hdM : orderOf x ∣ M := orderOf_dvd_of_pow_eq_one hxM
  have hd2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
  have hcop : Nat.Coprime M (2 ^ k) := (Nat.coprime_two_right.mpr hM).pow_right k
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdM hd2)

private theorem eq_one_of_mem_zL_of_isPGroup_two (hZ : Odd (Nat.card ↥(center ↥L))) {x : G}
    (hx : x ∈ zL L) (hx2 : IsPGroup 2 ↥(zpowers x)) : x = 1 := by
  have hxbot : x ∈ zL L ⊔ (⊥ : Subgroup G) := by rwa [sup_bot_eq]
  have h := mem_of_mem_zL_sup (L := L) hZ (V := ⊥) bot_le IsPGroup.of_bot hxbot hx2
  simpa using h

theorem actsTransitively_of_jSub [Group.IsPerfect ↥L] (hZ : Odd (Nat.card ↥(center ↥L)))
    {k : G} (hk : k ∈ L) {α : MulAut (L ⧸ center L)} (hkα : ActsAs L k α) {V W : Subgroup G}
    (hVL : V ≤ L) (hV2 : IsPGroup 2 ↥V) (hWV : W ≤ V)
    (hreg : Sec1.ActsRegularly (zpowers α) (jSub L V) (jSub L W)) :
    ActsTransitively (zpowers k) V W := by
  have hWL : W ≤ L := hWV.trans hVL
  have hW2 : IsPGroup 2 ↥W := hV2.to_le hWV
  have hknormV : k ∈ normalizer (V : Set G) :=
    (mem_normalizer_iff_jSub hZ hVL hV2 hkα).mpr (hreg.1 (Subgroup.mem_zpowers α))
  have hknormW : k ∈ normalizer (W : Set G) :=
    (mem_normalizer_iff_jSub hZ hWL hW2 hkα).mpr (hreg.2.1 (Subgroup.mem_zpowers α))
  refine ⟨Subgroup.zpowers_le.mpr hknormV, Subgroup.zpowers_le.mpr hknormW, ?_⟩
  intro u huV hnuW v hvV hnvW
  have huL : u ∈ L := hVL huV
  have hvL : v ∈ L := hVL hvV
  have hu2 : IsPGroup 2 ↥(zpowers u) := hV2.to_le (Subgroup.zpowers_le.mpr huV)
  have hv2 : IsPGroup 2 ↥(zpowers v) := hV2.to_le (Subgroup.zpowers_le.mpr hvV)
  let αu : MulAut (L ⧸ center L) :=
    MulAut.conj (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : L ⧸ center L)
  let αv : MulAut (L ⧸ center L) :=
    MulAut.conj (QuotientGroup.mk (⟨v, hvL⟩ : ↥L) : L ⧸ center L)
  have huα : ActsAs L u αu := actsAs_of_mem L huL
  have hvα : ActsAs L v αv := actsAs_of_mem L hvL
  have hmemu : αu ∈ jSub L V := (mem_jSub (V := V) (α := αu)).mpr ⟨u, huV, huα⟩
  have hmemv : αv ∈ jSub L V := (mem_jSub (V := V) (α := αv)).mpr ⟨v, hvV, hvα⟩
  have hnuW' : αu ∉ jSub L W := fun hmem =>
    hnuW ((mem_jSub_iff_mem hZ hWL hW2 huL hu2 huα).mp hmem)
  have hnvW' : αv ∉ jSub L W := fun hmem =>
    hnvW ((mem_jSub_iff_mem hZ hWL hW2 hvL hv2 hvα).mp hmem)
  obtain ⟨κ, ⟨hκmem, hκcond⟩, -⟩ := hreg.2.2 αu hmemu hnuW' αv hmemv hnvW'
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hκmem
  refine ⟨k ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩, ?_⟩
  have hknV : k ^ n ∈ normalizer (V : Set G) :=
    (Subgroup.zpowers_le.mpr hknormV) (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩)
  have hxV : v⁻¹ * (k ^ n * u * (k ^ n)⁻¹) ∈ V :=
    V.mul_mem (V.inv_mem hvV) ((Subgroup.mem_normalizer_iff.mp hknV u).mp huV)
  have hknL : k ^ n ∈ L := L.zpow_mem hk n
  have hxL : v⁻¹ * (k ^ n * u * (k ^ n)⁻¹) ∈ L :=
    L.mul_mem (L.inv_mem hvL) (L.mul_mem (L.mul_mem hknL huL) (L.inv_mem hknL))
  have hx2 : IsPGroup 2 ↥(zpowers (v⁻¹ * (k ^ n * u * (k ^ n)⁻¹))) :=
    hV2.to_le (Subgroup.zpowers_le.mpr hxV)
  have hxacts : ActsAs L (v⁻¹ * (k ^ n * u * (k ^ n)⁻¹)) (αv⁻¹ * (κ * αu * κ⁻¹)) := by
    have h1 : ActsAs L (k ^ n) (α ^ n) := actsAs_zpow' hkα n
    rw [hn] at h1
    exact actsAs_mul L (actsAs_inv L hvα)
      (actsAs_mul L (actsAs_mul L h1 huα) (actsAs_inv L h1))
  exact (mem_jSub_iff_mem hZ hWL hW2 hxL hx2 hxacts).mp hκcond

theorem isOrbitMod_of_jSub [Group.IsPerfect ↥L] (hZ : Odd (Nat.card ↥(center ↥L)))
    {A T Z : Subgroup G} {O : Set G} (hAL : A ≤ L) (hA2 : IsPGroup 2 ↥A) (hT : T ≤ normIn L A)
    (hZA : Z ≤ A) (hOA : O ⊆ A) {O' : Set (MulAut (L ⧸ center L))}
    (hO'A : O' ⊆ (jSub L A : Set (MulAut (L ⧸ center L))))
    (hOO' : ∀ w ∈ A, ∀ α : MulAut (L ⧸ center L), ActsAs L w α → (α ∈ O' ↔ w ∈ O))
    (h : IsOrbitMod (jSub L T) (jSub L Z) O') : IsOrbitMod T Z O := by
  obtain ⟨u', hu'O', hO'⟩ := h
  obtain ⟨u, huA, huα⟩ := (mem_jSub (V := A) (α := u')).mp (hO'A hu'O')
  have huO : u ∈ O := (hOO' u huA u' huα).mp hu'O'
  refine ⟨u, huO, ?_⟩
  apply Set.Subset.antisymm
  · intro w hwO
    have hwA : w ∈ A := hOA hwO
    let αw : MulAut (L ⧸ center L) :=
      MulAut.conj (QuotientGroup.mk (⟨w, hAL hwA⟩ : ↥L) : L ⧸ center L)
    have hwα : ActsAs L w αw := actsAs_of_mem L (hAL hwA)
    have hw'O' : αw ∈ O' := (hOO' w hwA αw hwα).mpr hwO
    rw [hO'] at hw'O'
    obtain ⟨κ, hκT, hκZ⟩ := hw'O'
    obtain ⟨t, htT, htκ⟩ := (mem_jSub (V := T) (α := κ)).mp hκT
    have htA : t ∈ normIn L A := hT htT
    have htL : t ∈ L := (Subgroup.mem_inf.mp htA).1
    have htnorm : t ∈ normalizer (A : Set G) := (Subgroup.mem_inf.mp htA).2
    have htutA : t * u * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp htnorm u).mp huA
    have hyA : (t * u * t⁻¹)⁻¹ * w ∈ A := A.mul_mem (A.inv_mem htutA) hwA
    have hyL : (t * u * t⁻¹)⁻¹ * w ∈ L := hAL hyA
    have hy2 : IsPGroup 2 ↥(zpowers ((t * u * t⁻¹)⁻¹ * w)) :=
      hA2.to_le (Subgroup.zpowers_le.mpr hyA)
    have hyα : ActsAs L ((t * u * t⁻¹)⁻¹ * w) ((κ * u' * κ⁻¹)⁻¹ * αw) := by
      have h1 : ActsAs L (t * u * t⁻¹) (κ * u' * κ⁻¹) :=
        actsAs_mul L (actsAs_mul L htκ huα) (actsAs_inv L htκ)
      exact actsAs_mul L (actsAs_inv L h1) hwα
    have hyZ : (t * u * t⁻¹)⁻¹ * w ∈ Z :=
      (mem_jSub_iff_mem hZ (hZA.trans hAL) (hA2.to_le hZA) hyL hy2 hyα).mp hκZ
    exact ⟨t, htT, hyZ⟩
  · intro w hw
    obtain ⟨t, htT, htZ⟩ := hw
    have htA : t ∈ normIn L A := hT htT
    have htL : t ∈ L := (Subgroup.mem_inf.mp htA).1
    have htnorm : t ∈ normalizer (A : Set G) := (Subgroup.mem_inf.mp htA).2
    have htutA : t * u * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp htnorm u).mp huA
    have hyA : (t * u * t⁻¹)⁻¹ * w ∈ A := hZA htZ
    have hwA : w ∈ A := by
      have h := A.mul_mem htutA hyA
      have h_eq : t * u * t⁻¹ * ((t * u * t⁻¹)⁻¹ * w) = w := by group
      rwa [h_eq] at h
    let αt : MulAut (L ⧸ center L) :=
      MulAut.conj (QuotientGroup.mk (⟨t, htL⟩ : ↥L) : L ⧸ center L)
    let αw : MulAut (L ⧸ center L) :=
      MulAut.conj (QuotientGroup.mk (⟨w, hAL hwA⟩ : ↥L) : L ⧸ center L)
    have htα : ActsAs L t αt := actsAs_of_mem L htL
    have hwα : ActsAs L w αw := actsAs_of_mem L (hAL hwA)
    have hyα : ActsAs L ((t * u * t⁻¹)⁻¹ * w) ((αt * u' * αt⁻¹)⁻¹ * αw) := by
      have h1 : ActsAs L (t * u * t⁻¹) (αt * u' * αt⁻¹) :=
        actsAs_mul L (actsAs_mul L htα huα) (actsAs_inv L htα)
      exact actsAs_mul L (actsAs_inv L h1) hwα
    have hκZ : (αt * u' * αt⁻¹)⁻¹ * αw ∈ jSub L Z :=
      (mem_jSub (V := Z) (α := (αt * u' * αt⁻¹)⁻¹ * αw)).mpr
        ⟨(t * u * t⁻¹)⁻¹ * w, htZ, hyα⟩
    have hαtT : αt ∈ jSub L T := (mem_jSub (V := T) (α := αt)).mpr ⟨t, htT, htα⟩
    have hw'O' : αw ∈ O' := by
      rw [hO']
      exact ⟨αt, hαtT, hκZ⟩
    exact (hOO' w hwA αw hwα).mp hw'O'

theorem splitsOver_jSub [Group.IsPerfect ↥L] (hZ : Odd (Nat.card ↥(center ↥L)))
    {N F : Subgroup G} (hNL : N ≤ L) (hFN : F ≤ N) (hF2 : IsPGroup 2 ↥F) (h : SplitsOver N F) :
    SplitsOver (jSub L N) (jSub L F) := by
  obtain ⟨C, hCN, hFC_inf, hFC_sup⟩ := h
  refine ⟨jSub L C, jSub_mono L hCN, ?_, ?_⟩
  · apply le_antisymm _ bot_le
    intro α hα
    rw [Subgroup.mem_inf] at hα
    obtain ⟨f, hfF, hfα⟩ := (mem_jSub (V := F) (α := α)).mp hα.1
    obtain ⟨c, hcC, hcα⟩ := (mem_jSub (V := C) (α := α)).mp hα.2
    have hfL : f ∈ L := hNL (hFN hfF)
    have hcL : c ∈ L := hNL (hCN hcC)
    have hz0acts : ActsAs L (f * c⁻¹) (1 : MulAut (L ⧸ center L)) := by
      simpa using actsAs_mul L hfα (actsAs_inv L hcα)
    have hz0L : f * c⁻¹ ∈ L := L.mul_mem hfL (L.inv_mem hcL)
    have hz0 : f * c⁻¹ ∈ zL L := (actsAs_one_iff_mem_zL hz0L).mp hz0acts
    have hz0cent : f * c⁻¹ ∈ centralizer (L : Set G) := (mem_zL_iff.mp hz0).2
    have hcomm : Commute (f * c⁻¹) c :=
      ((Subgroup.mem_centralizer_iff.mp hz0cent) c hcL).symm
    let M : ℕ := orderOf (f * c⁻¹)
    have hcard : Nat.card ↥(zL L) = Nat.card ↥(center ↥L) := by
      rw [zL, Subgroup.card_map_of_injective L.subtype_injective]
    have hM_odd : Odd M :=
      (hcard.symm ▸ hZ).of_dvd_nat (Subgroup.orderOf_dvd_natCard (zL L) hz0)
    have hf_eq : f = (f * c⁻¹) * c := by group
    have hpow : f ^ M = c ^ M := by
      have hzpow : (f * c⁻¹) ^ M = 1 := pow_orderOf_eq_one _
      rw [hf_eq, hcomm.mul_pow, hzpow, one_mul]
    have hcM_mem : c ^ M ∈ F ⊓ C := by
      refine ⟨?_, C.pow_mem hcC M⟩
      rw [← hpow]
      exact F.pow_mem hfF M
    have hcM_one : c ^ M = 1 := by
      rw [hFC_inf] at hcM_mem
      simpa using hcM_mem
    have hfM : f ^ M = 1 := hpow.trans hcM_one
    have hF2z : IsPGroup 2 ↥(zpowers f) := hF2.to_le (Subgroup.zpowers_le.mpr hfF)
    have hf_one : f = 1 := eq_one_of_pow_eq_one_of_odd hF2z hM_odd hfM
    have hα_one : ActsAs L 1 α := hf_one ▸ hfα
    have hα_eq : α = 1 := (actsAs_unique L (actsAs_one L) hα_one).symm
    rw [Subgroup.mem_bot]
    exact hα_eq
  · have hFnorm : F ≤ normalizer (L : Set G) :=
      (hFN.trans hNL).trans (Subgroup.le_normalizer (H := L))
    have hCnorm : C ≤ normalizer (L : Set G) :=
      (hCN.trans hNL).trans (Subgroup.le_normalizer (H := L))
    rw [← jSub_sup hFnorm hCnorm, hFC_sup]

theorem exists_conj_of_jSub [Group.IsPerfect ↥L] (hZ : Odd (Nat.card ↥(center ↥L)))
    {X : Subgroup G} (hXL : X ≤ L) (hX2 : IsPGroup 2 ↥X) {u v : G} (hu : u ∈ X) (hv : v ∈ X)
    {α β κ : MulAut (L ⧸ center L)} (hα : ActsAs L u α) (hβ : ActsAs L v β)
    (hκ : κ ∈ jSub L (normIn L X)) (h : κ * α * κ⁻¹ = β) :
    ∃ k ∈ normIn L X, k * u * k⁻¹ = v := by
  obtain ⟨k, hkX, hkκ⟩ := (mem_jSub (V := normIn L X) (α := κ)).mp hκ
  refine ⟨k, hkX, ?_⟩
  have hkL : k ∈ L := (Subgroup.mem_inf.mp hkX).1
  have hknorm : k ∈ normalizer (X : Set G) := (Subgroup.mem_inf.mp hkX).2
  have huL : u ∈ L := hXL hu
  have hvL : v ∈ L := hXL hv
  have hkukX : k * u * k⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hknorm u).mp hu
  have hkukα : ActsAs L (k * u * k⁻¹) (κ * α * κ⁻¹) :=
    actsAs_mul L (actsAs_mul L hkκ hα) (actsAs_inv L hkκ)
  have hc_acts : ActsAs L ((k * u * k⁻¹) * v⁻¹) 1 := by
    simpa [h] using actsAs_mul L hkukα (actsAs_inv L hβ)
  have hcL : (k * u * k⁻¹) * v⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem (L.mul_mem hkL huL) (L.inv_mem hkL)) (L.inv_mem hvL)
  have hc_zL : (k * u * k⁻¹) * v⁻¹ ∈ zL L := (actsAs_one_iff_mem_zL hcL).mp hc_acts
  have hcX : (k * u * k⁻¹) * v⁻¹ ∈ X := X.mul_mem hkukX (X.inv_mem hv)
  have hc2 : IsPGroup 2 ↥(zpowers ((k * u * k⁻¹) * v⁻¹)) :=
    hX2.to_le (Subgroup.zpowers_le.mpr hcX)
  have hc_one : (k * u * k⁻¹) * v⁻¹ = 1 :=
    eq_one_of_mem_zL_of_isPGroup_two hZ hc_zL hc2
  exact mul_inv_eq_one.mp hc_one

end CFSG.OddStandard.HigherRank.YamadaG23
