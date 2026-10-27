module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma47

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem relIndex_sup_eq_relIndex_inf_of_normalizes {H K : Subgroup G}
    (hK : H ≤ normalizer (K : Set G)) : H.relIndex (H ⊔ K) = (H ⊓ K).relIndex K := by
  have hKrel : K.relIndex (H ⊔ K) = (H ⊓ K).relIndex H := by
    set NG : Subgroup G := normalizer (K : Set G)
    have hHleNG : H ≤ NG := hK
    have hKleNG : K ≤ NG := le_normalizer
    have hHKleNG : H ⊔ K ≤ NG := sup_le hHleNG hKleNG
    have : (K.subgroupOf NG).Normal :=
      (normal_subgroupOf_iff_le_normalizer (H := K) (K := NG) hKleNG).2 le_rfl
    calc K.relIndex (H ⊔ K)
        = (K.subgroupOf NG).relIndex ((H ⊔ K).subgroupOf NG) :=
          (relIndex_subgroupOf (H := K) (K := H ⊔ K) (L := NG) hHKleNG).symm
      _ = (K.subgroupOf NG).relIndex ((H.subgroupOf NG) ⊔ (K.subgroupOf NG)) := by
          rw [subgroupOf_sup (A := H) (A' := K) (B := NG) hHleNG hKleNG]
      _ = (K.subgroupOf NG).relIndex (H.subgroupOf NG) :=
          relIndex_sup_right (H := H.subgroupOf NG) (K := K.subgroupOf NG)
      _ = ((H.subgroupOf NG) ⊓ (K.subgroupOf NG)).relIndex (H.subgroupOf NG) :=
          (inf_relIndex_left (H := H.subgroupOf NG) (K := K.subgroupOf NG)).symm
      _ = ((H ⊓ K).subgroupOf NG).relIndex (H.subgroupOf NG) := by
          rw [show (H.subgroupOf NG) ⊓ (K.subgroupOf NG) = (H ⊓ K).subgroupOf NG by
            ext x
            simp [mem_subgroupOf]]
      _ = (H ⊓ K).relIndex H := relIndex_subgroupOf (H := H ⊓ K) (K := H) (L := NG) hHleNG
  have hmul : (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) =
      (H ⊓ K).relIndex K * (H ⊓ K).relIndex H := by
    calc (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) = (H ⊓ K).relIndex (H ⊔ K) :=
          relIndex_mul_relIndex (H := H ⊓ K) (K := H) (L := H ⊔ K) inf_le_left le_sup_left
      _ = (H ⊓ K).relIndex K * K.relIndex (H ⊔ K) :=
          (relIndex_mul_relIndex (H := H ⊓ K) (K := K) (L := H ⊔ K) inf_le_right
            le_sup_right).symm
      _ = (H ⊓ K).relIndex K * (H ⊓ K).relIndex H := by rw [hKrel]
  have hpos : 0 < (H ⊓ K).relIndex H := Nat.pos_of_ne_zero (by
    dsimp [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite (H := (H ⊓ K).subgroupOf H))
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [hmul, Nat.mul_comm])

theorem card_sup_mul_inf_eq_mul_of_normalizes {H K : Subgroup G} (hK : H ≤ normalizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have h1 := relIndex_mul_card (H := H) (K := H ⊔ K)
  have h2 := relIndex_mul_card (H := H ⊓ K) (K := K)
  rw [inf_eq_left.mpr (le_sup_left : H ≤ H ⊔ K)] at h1
  rw [inf_eq_left.mpr (inf_le_right : H ⊓ K ≤ K)] at h2
  rw [relIndex_sup_eq_relIndex_inf_of_normalizes hK] at h1
  rw [← h1, ← h2]
  ring

theorem not_two_dvd_relIndex_of_isSylowTwoIn {P J : Subgroup G} (hP : IsSylowTwoIn P J) :
    ¬ 2 ∣ P.relIndex J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, T, hT⟩ := hP
  change ¬ 2 ∣ (P.subgroupOf J).index
  rw [← hT]
  exact T.not_dvd_index

omit [Finite G] in
theorem isSylowTwoIn_of_not_dvd {P H : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P)
    (h : ¬ 2 ∣ P.relIndex H) : IsSylowTwoIn P H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨hPH, (hP.of_equiv (subgroupOfEquivOfLe hPH).symm).toSylow h, rfl⟩

theorem isSylowTwoIn_inf_of_normal {S J K : Subgroup G}
    (hS : IsSylowTwoIn S (normalizer (J : Set G))) (hKN : K ≤ normalizer (J : Set G))
    (hNK : normalizer (J : Set G) ≤ normalizer (K : Set G)) : IsSylowTwoIn (S ⊓ K) K := by
  obtain ⟨hSN, T, hT⟩ := hS
  obtain ⟨R, hR⟩ := RankProjectiveAction.exists_sylow_inf_of_le_normalizer hSN ⟨T, hT⟩ hKN hNK
  exact ⟨inf_le_right, R, hR⟩

theorem isSylowTwoIn_withKernel {S J : Subgroup G}
    (hS : IsSylowTwoIn S (normalizer (J : Set G))) :
    IsSylowTwoIn (S ⊓ J ⊔ S ⊓ coreActionKernel J) (withKernel J) := by
  set K₀ : Subgroup G := coreActionKernel J with hK₀
  set P : Subgroup G := S ⊓ J with hPdef
  set Q : Subgroup G := S ⊓ K₀ with hQdef
  have hSN : S ≤ normalizer (J : Set G) := hS.1
  have hK₀N : K₀ ≤ normalizer (J : Set G) := fun c hc => (mem_coreActionKernel.mp hc).1
  have hNK₀ : normalizer (J : Set G) ≤ normalizer (K₀ : Set G) := fun n hn =>
    mem_normalizer_of_map_le_self (by
      rintro _ ⟨k, hk, rfl⟩
      exact conj_mem_coreActionKernel hn hk)
  have hJK₀N : J ⊓ K₀ ≤ normalizer (J : Set G) := inf_le_left.trans le_normalizer
  have hNJK₀ : normalizer (J : Set G) ≤ normalizer ((J ⊓ K₀ : Subgroup G) : Set G) :=
    fun n hn => inf_mem_normalizer hn (hNK₀ hn)
  have hP : IsSylowTwoIn P J := isSylowTwoIn_inf hS
  have hQ : IsSylowTwoIn Q K₀ := isSylowTwoIn_inf_of_normal hS hK₀N hNK₀
  have hZ : IsSylowTwoIn (S ⊓ (J ⊓ K₀)) (J ⊓ K₀) := isSylowTwoIn_inf_of_normal hS hJK₀N hNJK₀
  have hPQ : P ⊓ Q = S ⊓ (J ⊓ K₀) := by
    ext y
    simp only [hPdef, hQdef, mem_inf]
    tauto
  have hPQN : P ≤ normalizer (Q : Set G) := fun p hp =>
    inf_mem_normalizer (le_normalizer (mem_inf.mp hp).1)
      (hNK₀ (hSN (mem_inf.mp hp).1))
  have hJN : J ≤ normalizer (K₀ : Set G) := le_normalizer.trans hNK₀
  have hle : P ⊔ Q ≤ withKernel J := sup_le (inf_le_right.trans le_sup_left)
    (inf_le_right.trans le_sup_right)
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  refine isSylowTwoIn_of_not_dvd hle (hS2.to_le (sup_le inf_le_left inf_le_left)) ?_
  have e1 := card_sup_mul_inf_eq_mul_of_normalizes hJN
  have e2 := card_sup_mul_inf_eq_mul_of_normalizes hPQN
  have e3 := relIndex_mul_card (H := P ⊔ Q) (K := withKernel J)
  have e4 := relIndex_mul_card (H := P) (K := J)
  have e5 := relIndex_mul_card (H := Q) (K := K₀)
  have e6 := relIndex_mul_card (H := S ⊓ (J ⊓ K₀)) (K := J ⊓ K₀)
  rw [inf_eq_left.mpr hle] at e3
  rw [inf_eq_left.mpr hP.1] at e4
  rw [inf_eq_left.mpr hQ.1] at e5
  rw [inf_eq_left.mpr hZ.1] at e6
  rw [hPQ] at e2
  have hwk : withKernel J = J ⊔ K₀ := rfl
  rw [← hwk] at e1
  have hpos : 0 < Nat.card P * Nat.card Q := Nat.mul_pos Nat.card_pos Nat.card_pos
  have key : (P ⊔ Q).relIndex (withKernel J) * (S ⊓ (J ⊓ K₀)).relIndex (J ⊓ K₀) *
      (Nat.card P * Nat.card Q) = P.relIndex J * Q.relIndex K₀ * (Nat.card P * Nat.card Q) := by
    calc (P ⊔ Q).relIndex (withKernel J) * (S ⊓ (J ⊓ K₀)).relIndex (J ⊓ K₀) *
          (Nat.card P * Nat.card Q)
        = ((P ⊔ Q).relIndex (withKernel J) * Nat.card ↥(P ⊔ Q)) *
            ((S ⊓ (J ⊓ K₀)).relIndex (J ⊓ K₀) * Nat.card ↥(S ⊓ (J ⊓ K₀))) := by
          rw [← e2]; ring
      _ = Nat.card ↥(withKernel J) * Nat.card ↥(J ⊓ K₀) := by rw [e3, e6]
      _ = (P.relIndex J * Nat.card P) * (Q.relIndex K₀ * Nat.card Q) := by rw [e1, e4, e5]
      _ = P.relIndex J * Q.relIndex K₀ * (Nat.card P * Nat.card Q) := by ring
  have key' := Nat.eq_of_mul_eq_mul_right hpos key
  intro h2
  have h2' : 2 ∣ P.relIndex J * Q.relIndex K₀ := by
    rw [← key']
    exact h2.mul_right _
  rcases (Nat.prime_two.dvd_mul).mp h2' with h | h
  · exact not_two_dvd_relIndex_of_isSylowTwoIn hP h
  · exact not_two_dvd_relIndex_of_isSylowTwoIn hQ h

omit [Finite G] in
theorem commute_of_le_abelian {E F X : Subgroup G} (hX : ∀ u ∈ X, ∀ v ∈ X, u * v = v * u)
    (hEX : E ≤ X) (hFX : F ≤ X) : ∀ u ∈ E, ∀ v ∈ F, u * v = v * u :=
  fun u hu v hv => hX u (hEX hu) v (hFX hv)

theorem exists_connected_eight {P Q Z V : Subgroup G}
    (hPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hPQZ : P ⊓ Q = Z) (hVZ : V ≤ Z)
    (hV : IsElemTwo V) (hV4 : Nat.card V = 4)
    (hsq : ∀ u ∈ P, u * u ∈ Z → ∃ z ∈ Z, u * u = z * z)
    (hP' : ∃ p ∈ P, p ∉ Z ∧ p * p ∈ Z) {E : Subgroup G} (hEPQ : E ≤ P ⊔ Q)
    (hE : IsEightGroup E) :
    ∃ F : Subgroup G, F ≤ P ∧ IsEightGroup F ∧ AbelianConnected 3 E F := by
  have hZP : Z ≤ P := hPQZ ▸ inf_le_left
  have hZQ : Z ≤ Q := hPQZ ▸ inf_le_right
  have hVP : V ≤ P := hVZ.trans hZP
  have hVQ : V ≤ Q := hVZ.trans hZQ
  have hcen : ∀ v ∈ V, ∀ y ∈ P ⊔ Q, v * y = y * v := by
    intro v hv y hy
    have h1 : P ⊔ Q ≤ centralizer ({v} : Set G) := sup_le
      (fun p hp => mem_centralizer_singleton_iff.mpr (hPQ p hp v (hVQ hv)))
      (fun q hq => mem_centralizer_singleton_iff.mpr (hPQ v (hVP hv) q hq).symm)
    exact (mem_centralizer_singleton_iff.mp (h1 hy)).symm
  have hcen' : ∀ z ∈ Z, ∀ p ∈ P, z * p = p * z := fun z hz p hp => (hPQ p hp z (hZQ hz)).symm
  have hPN : P ≤ normalizer (Q : Set G) := fun p hp =>
    mem_normalizer_of_forall_commute fun q hq => hPQ p hp q hq
  have hVE : ¬ E ≤ V := fun h => by
    have := card_le_of_le h
    rw [hE.2, hV4] at this
    omega
  obtain ⟨w, hwE, hwV⟩ := Set.not_subset.mp hVE
  have hw2 : w * w = 1 := hE.1.2 w hwE
  have hwPQ : w ∈ P ⊔ Q := hEPQ hwE
  have hwc : ∀ e ∈ V, e * w = w * e := fun e he => hcen e he w hwPQ
  obtain ⟨hA₁, hA₁c⟩ := isElemTwo_sup_zpowers hV hw2 hwV hwc
  set A₁ : Subgroup G := V ⊔ zpowers w with hA₁def
  have hA₁8 : IsEightGroup A₁ := ⟨hA₁, by rw [hA₁c, hV4]⟩
  have hEV : IsElemTwo (E ⊔ V) := hE.1.sup hV fun u hu v hv =>
    (hcen v hv u (hEPQ hu)).symm
  have hEA₁ : ∀ u ∈ E, ∀ v ∈ A₁, u * v = v * u :=
    commute_of_le_abelian hEV.1 le_sup_left
      (sup_le le_sup_right (zpowers_le.mpr (mem_sup_left hwE)))
  have hrank : ∀ F : Subgroup G, IsEightGroup F → IsAbelianTwoOfRank 3 F := fun F hF =>
    hF.1.isAbelianTwoOfRank (by rw [hF.2])
  suffices h : ∃ F : Subgroup G, F ≤ P ∧ IsEightGroup F ∧ ∀ u ∈ A₁, ∀ v ∈ F, u * v = v * u by
    obtain ⟨F, hFP, hF, hA₁F⟩ := h
    exact ⟨F, hFP, hF, hrank E hE, (Relation.ReflTransGen.single ⟨hrank A₁ hA₁8, hEA₁⟩).tail
      ⟨hrank F hF, hA₁F⟩⟩
  have hw' : w ∈ (P : Set G) * (Q : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right P Q hPN]
    exact hwPQ
  obtain ⟨u, hu, q, hq, hwuq⟩ := hw'
  have hwuq' : w = u * q := hwuq.symm
  have huq := hPQ u hu q hq
  have hu2 : u * u = (q * q)⁻¹ := by
    have h1 : u * q * (u * q) = u * u * (q * q) := by
      calc u * q * (u * q) = u * (q * u) * q := by group
        _ = u * (u * q) * q := by rw [huq]
        _ = u * u * (q * q) := by group
    rw [hwuq', h1] at hw2
    exact eq_inv_of_mul_eq_one_left hw2
  have huuZ : u * u ∈ Z := by
    rw [← hPQZ]
    refine mem_inf.mpr ⟨mul_mem hu hu, ?_⟩
    rw [hu2]
    exact inv_mem (mul_mem hq hq)
  have hinv : ∀ p ∈ P, p * p ∈ Z → ∃ p₁ ∈ P, p₁ * p₁ = 1 ∧ p * p₁⁻¹ ∈ Z := by
    intro p hp hpZ
    obtain ⟨z, hz, hzz⟩ := hsq p hp hpZ
    have hzp : z * p = p * z := (hcen' z hz p hp)
    refine ⟨z⁻¹ * p, mul_mem (inv_mem (hZP hz)) hp, ?_, ?_⟩
    · calc z⁻¹ * p * (z⁻¹ * p) = z⁻¹ * (p * z⁻¹) * p := by group
        _ = z⁻¹ * (z⁻¹ * p) * p := by
          rw [show p * z⁻¹ = z⁻¹ * p by
            calc p * z⁻¹ = z⁻¹ * (z * p) * z⁻¹ := by group
              _ = z⁻¹ * (p * z) * z⁻¹ := by rw [hzp]
              _ = z⁻¹ * p := by group]
        _ = (z * z)⁻¹ * (p * p) := by group
        _ = 1 := by rw [← hzz, inv_mul_cancel]
    · rw [show p * (z⁻¹ * p)⁻¹ = p * p⁻¹ * z by group, mul_inv_cancel, one_mul]
      exact hz
  have hrank8 : ∀ F : Subgroup G, F ≤ P → ∀ p₁ ∈ P, p₁ * p₁ = 1 → p₁ ∉ V →
      F = V ⊔ zpowers p₁ → IsEightGroup F := by
    rintro F - p₁ hp₁ hp₁2 hp₁V rfl
    obtain ⟨hF, hFc⟩ := isElemTwo_sup_zpowers hV hp₁2 hp₁V fun e he =>
      hcen e he p₁ (mem_sup_left hp₁)
    exact ⟨hF, by rw [hFc, hV4]⟩
  obtain ⟨u₁, hu₁P, hu₁2, hu₁Z⟩ := hinv u hu huuZ
  by_cases hu₁V : u₁ ∈ V
  ·
    have huZ : u ∈ Z := by
      have := mul_mem hu₁Z (hVZ hu₁V)
      rwa [inv_mul_cancel_right] at this
    have hwQ : w ∈ Q := by
      rw [hwuq']
      exact mul_mem (hZQ huZ) hq
    have hA₁Q : A₁ ≤ Q := sup_le hVQ (zpowers_le.mpr hwQ)
    obtain ⟨p', hp'P, hp'Z, hp'2⟩ := hP'
    obtain ⟨p₁, hp₁P, hp₁2, hp₁Z⟩ := hinv p' hp'P hp'2
    have hp₁V : p₁ ∉ V := fun h => hp'Z (by
      have := mul_mem hp₁Z (hVZ h)
      rwa [inv_mul_cancel_right] at this)
    refine ⟨V ⊔ zpowers p₁, sup_le hVP (zpowers_le.mpr hp₁P),
      hrank8 _ (sup_le hVP (zpowers_le.mpr hp₁P)) p₁ hp₁P hp₁2 hp₁V rfl, ?_⟩
    intro x hx y hy
    exact (hPQ y (sup_le hVP (zpowers_le.mpr hp₁P) hy) x (hA₁Q hx)).symm
  ·
    have hFP : V ⊔ zpowers u₁ ≤ P := sup_le hVP (zpowers_le.mpr hu₁P)
    refine ⟨V ⊔ zpowers u₁, hFP, hrank8 _ hFP u₁ hu₁P hu₁2 hu₁V rfl, ?_⟩
    have hzu : u * u₁ = u₁ * u := by
      set z := u * u₁⁻¹ with hz
      have hzu₁ := hcen' z hu₁Z u₁ hu₁P
      calc u * u₁ = z * u₁ * u₁ := by rw [hz]; group
        _ = u₁ * z * u₁ := by rw [hzu₁]
        _ = u₁ * u := by rw [hz]; group
    have hwu₁ : w * u₁ = u₁ * w := by
      rw [hwuq']
      calc u * q * u₁ = u * (q * u₁) := by group
        _ = u * (u₁ * q) := by rw [hPQ u₁ hu₁P q hq]
        _ = u₁ * (u * q) := by rw [← mul_assoc, hzu, mul_assoc]
    have hFC : V ⊔ zpowers u₁ ≤ centralizer (A₁ : Set G) := by
      have hA₁C : A₁ ≤ centralizer ((V ⊔ zpowers u₁ : Subgroup G) : Set G) := by
        refine sup_le (fun e he => ?_) (zpowers_le.mpr ?_)
        · rw [mem_centralizer_iff]
          intro y hy
          exact (hcen e he y (sup_le hVP (zpowers_le.mpr hu₁P) hy |> mem_sup_left)).symm
        · rw [mem_centralizer_iff]
          intro y hy
          have hyC : V ⊔ zpowers u₁ ≤ centralizer ({w} : Set G) := sup_le
            (fun e he => mem_centralizer_singleton_iff.mpr (hwc e he))
            (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hwu₁.symm))
          exact mem_centralizer_singleton_iff.mp (hyC hy)
      intro y hy
      rw [mem_centralizer_iff]
      intro x hx
      exact ((mem_centralizer_iff.mp (hA₁C hx)) y hy).symm
    intro x hx y hy
    exact (mem_centralizer_iff.mp (hFC hy)) x hx

omit [Finite G] in
theorem relIndex_zStarIn_eq {J : Subgroup G}
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) : (zStarIn J).relIndex J = 20160 := by
  obtain ⟨e⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hL34
  have h1 : (zStarIn J).subgroupOf J = Open.fusionZStar J :=
    comap_map_eq_self_of_injective J.subtype_injective _
  rw [relIndex, h1, index, Nat.card_congr e.toEquiv, PSL3Four.card_S]

theorem exists_not_mem_sq_mem_zStarIn {J P : Subgroup G}
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) (hP : IsSylowTwoIn P J) :
    ∃ p ∈ P, p ∉ zStarIn J ∧ p * p ∈ zStarIn J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot : ¬ P ≤ zStarIn J := by
    intro hle
    have h1 : (zStarIn J).relIndex J ∣ P.relIndex J := relIndex_dvd_of_le_left J hle
    rw [relIndex_zStarIn_eq hL34] at h1
    exact not_two_dvd_relIndex_of_isSylowTwoIn hP (dvd_trans (by norm_num) h1)
  obtain ⟨p₀, hp₀P, hp₀Z⟩ := Set.not_subset.mp hnot
  obtain ⟨n, hn⟩ := (isPGroup_of_isSylowTwoIn hP) ⟨p₀, hp₀P⟩
  have hex : ∃ k, p₀ ^ (2 ^ k) ∈ zStarIn J := ⟨n, by
    have := congrArg Subtype.val hn
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    rw [this]
    exact one_mem _⟩
  set k := Nat.find hex with hk
  have hk0 : k ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hk, h0, pow_zero, pow_one] at this
    exact hp₀Z this
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hmin : ¬ p₀ ^ (2 ^ m) ∈ zStarIn J := Nat.find_min hex (by omega)
  refine ⟨p₀ ^ (2 ^ m), pow_mem hp₀P _, hmin, ?_⟩
  have := Nat.find_spec hex
  rw [← hk, hm, pow_succ, pow_mul, pow_two] at this
  exact this

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS GrS4

theorem l34Lemma46WStep_of_inputs
    (hSol : SolomonCommutingCoreInput) (hSqZ : L34SquareCenterFact)
    (hConnJ : L34EightsConnectedFact) : L34Lemma46WStep := by
  intro G _ _ a x J S A hset hrun hexp hnc E hEW hE8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbase, hU3, hL34, -, hS, -, -⟩ := id hset
  obtain ⟨-, -, -, -, -, hLB, -, -⟩ := hbase
  obtain ⟨hAW, hA8, hWA⟩ := hrun
  have hGW : GWTwoBalanced G := gwTwoBalanced_of_locallyTwoBalanced hSol hLB
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hU3.2.2.2.2.1
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  set P : Subgroup G := S ⊓ J with hPdef
  set Q : Subgroup G := S ⊓ coreActionKernel J with hQdef
  set Z : Subgroup G := S ⊓ zStarIn J with hZdef
  have hP : IsSylowTwoIn P J := isSylowTwoIn_inf hS
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : P ⊓ zStarIn J = Z := by rw [hPdef, inf_assoc, inf_eq_right.mpr hZJ]
  have hzK : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
  have hPQZ : P ⊓ Q = Z := by
    rw [hPdef, hQdef, hZdef, hzK]
    ext y
    simp only [mem_inf]
    tauto
  have hPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p := fun p hp q hq =>
    commute_of_mem_coreActionKernel hS2 hp hq
  have hZcomm : ∀ u ∈ Z, ∀ v ∈ Z, u * v = v * u := fun u hu v hv =>
    hPQ u ((hPQZ ▸ inf_le_left : Z ≤ P) hu) v ((hPQZ ▸ inf_le_right : Z ≤ Q) hv)
  obtain ⟨u, hu, v, hv, hu2, hv2, hu1, hv1, huv⟩ :=
    exists_two_involutions (hS2.to_le inf_le_left) hZcomm hnc
  have hvu : v ∉ zpowers u := fun h => by
    rcases eq_one_or_eq_of_mem_zpowers hu2 h with h | h
    · exact hv1 h
    · exact huv h.symm
  obtain ⟨hV, hVc⟩ := isElemTwo_sup_zpowers (isElemTwo_zpowers hu2) hv2 hvu fun e he => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp he
    exact (Commute.zpow_left (show Commute u v from hZcomm u hu v hv) i).eq
  set V : Subgroup G := zpowers u ⊔ zpowers v with hVdef
  have hV4 : Nat.card V = 4 := by
    rw [hVc, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1]
  have hVZ : V ≤ Z := sup_le (zpowers_le.mpr hu) (zpowers_le.mpr hv)
  have hsq : ∀ w ∈ P, w * w ∈ Z → ∃ z ∈ Z, w * w = z * z := by
    intro w hw hwZ
    obtain ⟨z, hz, hzz⟩ := hSqZ G J P hJper hL34 hP w hw (mem_inf.mp hwZ).2
    exact ⟨z, hZP ▸ hz, hzz⟩
  have hP' : ∃ p ∈ P, p ∉ Z ∧ p * p ∈ Z := by
    obtain ⟨p, hp, hpZ, hp2⟩ := exists_not_mem_sq_mem_zStarIn hL34 hP
    exact ⟨p, hp, fun h => hpZ (mem_inf.mp h).2,
      mem_inf.mpr ⟨mul_mem (mem_inf.mp hp).1 (mem_inf.mp hp).1, hp2⟩⟩
  have hSyl := isSylowTwoIn_withKernel hS
  have hconj : ∀ B : Subgroup G, B ≤ withKernel J → IsEightGroup B →
      ∃ c : G, B.map (MulAut.conj c).toMonoidHom ≤ P ⊔ Q ∧
        IsEightGroup (B.map (MulAut.conj c).toMonoidHom) := by
    intro B hBW hB
    obtain ⟨c, -, hc⟩ := hSyl.exists_conj_le hBW hB.1.isPGroup
    refine ⟨c, ?_, hB.1.map_conj c, by rw [card_map_of_injective (MulAut.conj c).injective, hB.2]⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hc y hy
  obtain ⟨c, hcA, hcA8⟩ := hconj A hAW hA8
  obtain ⟨d, hdE, hdE8⟩ := hconj E hEW hE8
  obtain ⟨FA, hFAP, hFA, hAFA⟩ := exists_connected_eight hPQ hPQZ hVZ hV hV4 hsq hP' hcA hcA8
  obtain ⟨FE, hFEP, hFE, hEFE⟩ := exists_connected_eight hPQ hPQZ hVZ hV hV4 hsq hP' hdE hdE8
  obtain ⟨j, -, hj⟩ := hConnJ G J P hJper hL34 hP (by rwa [hZP])
    (by rw [hZP]; exact exists_sq_ne_one_of_exponent_eq_four hexp) FA FE hFAP hFEP hFA hFE
  have h1 := wGroup_eq_of_abelianConnected hGW hAFA
  have h2 := wGroup_eq_of_abelianConnected hGW hj.abelianConnected
  have h3 := wGroup_eq_of_abelianConnected hGW hEFE
  rw [wGroup_map_conj] at h1 h3
  rw [wGroup_conjugate, ← h3] at h2
  intro hE0
  apply hWA
  rw [hE0] at h2
  have h4 : (wGroup A).map (MulAut.conj c).toMonoidHom = ⊥ := by
    rw [h1, h2]
    simp [conjugate]
  exact (map_eq_bot_iff_of_injective _ (MulAut.conj c).injective).mp h4

end CFSG.ComponentClassification.GrSLit
