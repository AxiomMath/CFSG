module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsOutInv
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InvClsZ4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Fusion
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Tools46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS2

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem inverts_of_normalizer_conj (hOut : L34OutSquareFact) {J S : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J))
    (hS : IsSylowTwoIn S (normalizer (J : Set G))) (hZc : IsCyclic ↥(S ⊓ zStarIn J))
    (hZ4 : Nat.card ↥(S ⊓ zStarIn J) = 4) {a b n : G} (haZ : a ∈ S ⊓ zStarIn J)
    (haa : a * a = 1) (ha1 : a ≠ 1) (hSa : ∀ s ∈ S, s * a = a * s) (hbS : b ∈ S)
    (hbK : b ∉ withKernel J)
    (hn : n ∈ normalizer ((S ⊓ centralizer ({b} : Set G) : Subgroup G) : Set G))
    (hbn : n⁻¹ * b * n = a) : ∀ z ∈ S ⊓ zStarIn J, b * z * b⁻¹ = z⁻¹ := by
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  obtain ⟨g, hg⟩ := hZc.exists_generator
  set z₀ : G := (g : G) with hz₀
  have hz₀Z : z₀ ∈ S ⊓ zStarIn J := g.2
  have hg4 : orderOf g = 4 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hZ4]
  have hz₀4 : z₀ ^ 4 = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg4] at h
    exact congrArg Subtype.val h
  have hZab : ∀ u ∈ S ⊓ zStarIn J, ∀ v ∈ S ⊓ zStarIn J, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := ↥(S ⊓ zStarIn J))).is_comm.comm
      (⟨u, hu⟩ : ↥(S ⊓ zStarIn J)) ⟨v, hv⟩)
  have hz₀a : z₀ * z₀ = a := by
    have hsq : z₀ * z₀ * (z₀ * z₀) = 1 := by
      rw [← hz₀4]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rcases eq_one_or_eq_of_isCyclic hZc haZ (mul_mem hz₀Z hz₀Z) haa ha1 hsq with h | h
    · exfalso
      have h2 : g ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact h)
      have := orderOf_le_of_pow_eq_one (by norm_num) h2
      omega
    · exact h
  set y : G := b * z₀ * b⁻¹ with hy
  have hyZ : y ∈ S ⊓ zStarIn J :=
    mem_inf.mpr ⟨mul_mem (mul_mem hbS (mem_inf.mp hz₀Z).1) (inv_mem hbS),
      conj_mem_zStarIn (hS.1 hbS) (mem_inf.mp hz₀Z).2⟩
  have hyy : y * y = a := by
    rw [hy, show b * z₀ * b⁻¹ * (b * z₀ * b⁻¹) = b * (z₀ * z₀) * b⁻¹ by group, hz₀a,
      hSa b hbS, mul_inv_cancel_right]
  have hw : z₀⁻¹ * y * (z₀⁻¹ * y) = 1 := by
    have hc : y * z₀⁻¹ = z₀⁻¹ * y := hZab y hyZ _ (inv_mem hz₀Z)
    calc z₀⁻¹ * y * (z₀⁻¹ * y) = z₀⁻¹ * (y * z₀⁻¹) * y := by group
      _ = z₀⁻¹ * z₀⁻¹ * (y * y) := by rw [hc]; group
      _ = 1 := by rw [hyy, ← hz₀a]; group
  rcases eq_one_or_eq_of_isCyclic hZc haZ (mul_mem (inv_mem hz₀Z) hyZ) haa ha1 hw with h | h
  ·
    exfalso
    have hyz : b * z₀ * b⁻¹ = z₀ := by
      calc b * z₀ * b⁻¹ = z₀ * (z₀⁻¹ * y) := by rw [hy]; group
        _ = z₀ := by rw [h, mul_one]
    have hz₀X : z₀ ∈ S ⊓ centralizer ({b} : Set G) := mem_inf.mpr ⟨(mem_inf.mp hz₀Z).1,
      mem_centralizer_singleton_iff.mpr (by
        calc z₀ * b = b * z₀ * b⁻¹ * b := by rw [hyz]
          _ = b * z₀ := by group)⟩
    have hsX := (mem_normalizer_iff.mp hn z₀).mp hz₀X
    have hsS : n * z₀ * n⁻¹ ∈ S := (mem_inf.mp hsX).1
    have hsq := hOut G J hJ hL _ (hS.1 hsS) (hS2.to_le (zpowers_le.mpr hsS))
    apply hbK
    rw [show b = n * z₀ * n⁻¹ * (n * z₀ * n⁻¹) by
      rw [show n * z₀ * n⁻¹ * (n * z₀ * n⁻¹) = n * (z₀ * z₀) * n⁻¹ by group, hz₀a, ← hbn]
      group]
    exact hsq
  ·
    have hyi : b * z₀ * b⁻¹ = z₀⁻¹ := by
      calc b * z₀ * b⁻¹ = z₀ * (z₀⁻¹ * y) := by rw [hy]; group
        _ = z₀ * a := by rw [h]
        _ = z₀⁻¹ := by
          rw [← hz₀a]
          calc z₀ * (z₀ * z₀) = z₀ ^ 4 * z₀⁻¹ := by
                simp only [pow_succ, pow_zero, one_mul, mul_assoc, mul_inv_cancel, mul_one]
            _ = z₀⁻¹ := by rw [hz₀4, one_mul]
    intro z hz
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨z, hz⟩)
    have hzk : z = z₀ ^ k := by
      have := congrArg Subtype.val hk
      rw [Subgroup.coe_zpow] at this
      exact this.symm
    rw [hzk, ← conj_zpow, hyi, inv_zpow]

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS GrS4

abbrev L34OuterInvolutionCenterInvLocal {G : Type} [Group G] (J S : Subgroup G) (a b : G) :
    Prop :=
  (∀ y ∈ S ⊓ centralizer ({b} : Set G),
      (∀ t ∈ S ⊓ centralizer ({b} : Set G), y * t = t * y) → y * y = 1 →
        y ∈ J ∨ b * y ∈ J) ∧
    (∃ z ∈ J ⊓ (S ⊓ centralizer ({b} : Set G)),
        (∀ t ∈ S ⊓ centralizer ({b} : Set G), z * t = t * z) ∧
          z * z = 1 ∧ z ≠ 1 ∧ z ≠ a) ∧
    ∀ z ∈ J ⊓ (S ⊓ centralizer ({b} : Set G)),
      (∀ t ∈ S ⊓ centralizer ({b} : Set G), z * t = t * z) → z * z = 1 →
        ∃ s ∈ S, s⁻¹ * b * s = b * z

theorem l34EndFusionStep_of_localData
    {G : Type} [Group G] [Finite G]
    {a : G} {J S : Subgroup G}
    (hsimple : IsSimpleGroup G) (hnab : ∃ u v : G, u * v ≠ v * u)
    (hInvLocal : ∀ b : G, b ∈ S → b * b = 1 → b ∉ withKernel J →
      (∀ z ∈ S ⊓ zStarIn J, b * z * b⁻¹ = z⁻¹) →
      L34OuterInvolutionCenterInvLocal J S a b)
    (hOut : L34OutSquareFact)
    (hJ : ⁅J, J⁆ = J)
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J))
    (hS : IsSylowTwoIn S (normalizer (J : Set G)))
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S)
    (hcent : ∀ s ∈ S, s * a = a * s) (ha2 : orderOf a = 2)
    (hZc : IsCyclic ↥(S ⊓ zStarIn J))
    (hZ4 : Nat.card ↥(S ⊓ zStarIn J) = 4)
    (haZ : a ∈ S ⊓ zStarIn J)
    (hinv : ∀ y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J, y * y = 1 → y ∈ S ⊓ J) :
    ∃ g : G, g⁻¹ * a * g ∈ S ⊓ J ∧ g⁻¹ * a * g ≠ a := by
  obtain ⟨T, hTS⟩ := hSyl
  by_contra hno
  push Not at hno
  have haS : a ∈ S := (mem_inf.mp haZ).1
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have haT : a ∈ (T : Subgroup G) := by rw [hTS]; exact haS
  have hcentT : ∀ s ∈ (T : Subgroup G), s * a = a * s := by rw [hTS]; exact hcent
  have hne : ∃ g : G, g⁻¹ * a * g ∈ (T : Subgroup G) ∧ g⁻¹ * a * g ≠ a := by
    by_contra h
    push Not at h
    exact false_of_isolated_two_central hnab T haT hcentT ha2 h
  obtain ⟨b, hbT, hba, ⟨g, hg⟩, n, hn, hbn⟩ :=
    exists_extremal_normalizer_conj T (fun s hs => (hcentT s hs).symm) hne
  rw [hTS] at hbT hn
  have hbb : b * b = 1 := by
    rw [hg, show g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g by group, haa]
    group
  have hbJ : b ∉ J := by
    intro h
    apply hba
    rw [hg]
    apply hno g
    rw [← hg]
    exact mem_inf.mpr ⟨hbT, h⟩
  have hbK : b ∉ withKernel J := by
    intro hbW
    have hPQ := isSylowTwoIn_withKernel hS
    have hle : S ⊓ J ⊔ S ⊓ coreActionKernel J ≤ S ⊓ withKernel J :=
      sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
    have heq := hPQ.eq_of_le hle inf_le_right
      ((isPGroup_of_isSylowTwoIn hS).to_le inf_le_left)
    have hb1 : b ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J := by
      rw [← heq]
      exact mem_inf.mpr ⟨hbT, hbW⟩
    exact hbJ (mem_inf.mp (hinv b hb1 hbb)).2
  have hbinv := inverts_of_normalizer_conj hOut hJ hL34 hS hZc hZ4 haZ haa ha1 hcent hbT hbK hn
    hbn
  obtain ⟨h1, ⟨z, hzJX, hzZ, hz2, hz1, hza⟩, h3⟩ :=
    hInvLocal b hbT hbb hbK hbinv
  set X : Subgroup G := S ⊓ centralizer ({b} : Set G) with hXdef
  have hbX : b ∈ X := mem_inf.mpr ⟨hbT, mem_centralizer_singleton_iff.mpr rfl⟩
  have hbZ : ∀ t ∈ X, b * t = t * b := fun t ht =>
    (mem_centralizer_singleton_iff.mp (mem_inf.mp ht).2).symm
  have hkey : ∀ y ∈ X, (∀ t ∈ X, y * t = t * y) → y * y = 1 →
      (¬ ∃ h : G, y = h⁻¹ * a * h) → y ∈ J := by
    intro y hyX hyZ hy2 hyna
    rcases h1 y hyX hyZ hy2 with hyJ | hbyJ
    · exact hyJ
    · exfalso
      have hby : b * y = y * b := hbZ y hyX
      have hbyX : b * y ∈ X := mul_mem hbX hyX
      have hbyZ : ∀ t ∈ X, b * y * t = t * (b * y) := fun t ht => by
        rw [mul_assoc, hyZ t ht, ← mul_assoc, hbZ t ht, mul_assoc]
      have hby2 : b * y * (b * y) = 1 := by
        rw [show b * y * (b * y) = b * (y * b) * y by group, ← hby,
          show b * (b * y) * y = (b * b) * (y * y) by group, hbb, hy2, one_mul]
      obtain ⟨s, -, hs⟩ := h3 (b * y) (mem_inf.mpr ⟨hbyJ, hbyX⟩) hbyZ hby2
      apply hyna
      refine ⟨g * s, ?_⟩
      rw [show y = b * (b * y) by rw [← mul_assoc, hbb, one_mul], ← hs, hg]
      group
  have hzX : z ∈ X := (mem_inf.mp hzJX).2
  have hzJ : z ∈ J := (mem_inf.mp hzJX).1
  have hzS : z ∈ S := (mem_inf.mp hzX).1
  have haX : a ∈ X := mem_inf.mpr ⟨haS, mem_centralizer_singleton_iff.mpr (hcent b hbT).symm⟩
  have haZX : ∀ t ∈ X, a * t = t * a := fun t ht => (hcent t (mem_inf.mp ht).1).symm
  have hzaX : z * a ∈ X := mul_mem hzX haX
  have hzaZ : ∀ t ∈ X, z * a * t = t * (z * a) := fun t ht => by
    rw [mul_assoc, haZX t ht, ← mul_assoc, hzZ t ht, mul_assoc]
  have hza2 : z * a * (z * a) = 1 := by
    rw [show z * a * (z * a) = z * (a * z) * a by group, haZX z hzX,
      show z * (z * a) * a = (z * z) * (a * a) by group, hz2, haa, one_mul]
  have hzna : ¬ ∃ h : G, z = h⁻¹ * a * h := by
    rintro ⟨h, hh⟩
    exact hza (by rw [hh]; exact hno h (by rw [← hh]; exact mem_inf.mpr ⟨hzS, hzJ⟩))
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have haJ : a ∈ J := hZJ (mem_inf.mp haZ).2
  have hzana : ¬ ∃ h : G, z * a = h⁻¹ * a * h := by
    rintro ⟨h, hh⟩
    have h2 := hno h (by rw [← hh]; exact mem_inf.mpr ⟨mul_mem hzS haS, mul_mem hzJ haJ⟩)
    rw [← hh] at h2
    apply hz1
    calc z = z * a * a⁻¹ := by group
      _ = a * a⁻¹ := by rw [h2]
      _ = 1 := mul_inv_cancel a
  have hconj : ∀ m ∈ normalizer (X : Set G), ∀ y ∈ X, (∀ t ∈ X, y * t = t * y) →
      y * y = 1 → (¬ ∃ h : G, y = h⁻¹ * a * h) → m⁻¹ * y * m ∈ S ⊓ J := by
    intro m hm y hyX hyZ hy2 hyna
    have hm' : m⁻¹ ∈ normalizer (X : Set G) := inv_mem hm
    have hy'X : m⁻¹ * y * m ∈ X := by
      have := (mem_normalizer_iff.mp hm' y).mp hyX
      rwa [inv_inv] at this
    have hy'Z : ∀ t ∈ X, m⁻¹ * y * m * t = t * (m⁻¹ * y * m) := by
      intro t ht
      have ht' : m * t * m⁻¹ ∈ X := (mem_normalizer_iff.mp hm t).mp ht
      have hc := hyZ _ ht'
      calc m⁻¹ * y * m * t = m⁻¹ * (y * (m * t * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * t * m⁻¹) * y) * m := by rw [hc]
        _ = t * (m⁻¹ * y * m) := by group
    have hy'2 : m⁻¹ * y * m * (m⁻¹ * y * m) = 1 := by
      rw [show m⁻¹ * y * m * (m⁻¹ * y * m) = m⁻¹ * (y * y) * m by group, hy2]
      group
    have hy'na : ¬ ∃ h : G, m⁻¹ * y * m = h⁻¹ * a * h := by
      rintro ⟨h, hh⟩
      exact hyna ⟨h * m⁻¹, by
        rw [show y = m * (m⁻¹ * y * m) * m⁻¹ by group, hh]
        group⟩
    exact mem_inf.mpr ⟨(mem_inf.mp hy'X).1, hkey _ hy'X hy'Z hy'2 hy'na⟩
  have hfix : ∀ m ∈ normalizer (X : Set G), m⁻¹ * a * m = a := by
    intro m hm
    have hz' := hconj m hm z hzX hzZ hz2 hzna
    have hw' := hconj m hm (z * a) hzaX hzaZ hza2 hzana
    have e : m⁻¹ * a * m = (m⁻¹ * z * m) * (m⁻¹ * (z * a) * m) := by
      rw [show (m⁻¹ * z * m) * (m⁻¹ * (z * a) * m) = m⁻¹ * ((z * z) * a) * m by group, hz2,
        one_mul]
    exact hno m (by rw [e]; exact mul_mem hz' hw')
  apply hba
  have h4 := hfix n⁻¹ (inv_mem hn)
  rw [inv_inv] at h4
  calc b = n * (n⁻¹ * b * n) * n⁻¹ := by group
    _ = n * a * n⁻¹ := by rw [hbn]
    _ = a := h4

theorem l34EndFusionStep_of_invStep (hInv : L34OuterInvolutionCenterInvStep)
    (hOut : L34OutSquareFact) : L34EndFusionStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl
  obtain ⟨T, hTS⟩ := hSyl
  obtain ⟨hbase, hU3, hL34, -, hS, haS, -⟩ := id hset
  obtain ⟨hsimple, hnab, -, -, -, -, -, -⟩ := hbase
  have hJ : ⁅J, J⁆ = J := GSThmB.commutator_eq_self_of_isPComponent hU3.2.2.2.1 hU3.2.2.2.2.1
  have ha2 : orderOf a = 2 := hU3.1
  have hZne : S ⊓ zStarIn J ≠ ⊥ := by
    intro hbot
    rw [hbot, card_bot] at hZ4
    norm_num at hZ4
  have haZ : a ∈ S ⊓ zStarIn J := hZ hZne
  exact l34EndFusionStep_of_localData hsimple hnab
    (fun b hbS hbb hbK hbinv =>
      hInv G a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv ⟨T, hTS⟩ b hbS hbb hbK hbinv)
    hOut hJ hL34 hS ⟨T, hTS⟩ hcent ha2 hZc hZ4 haZ hinv

end CFSG.ComponentClassification.GrSLit
