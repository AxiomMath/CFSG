module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify
public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import Certificates.Certificate23100
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43

theorem QT0_valid :
    QT0.check = true ∧ QT0.orderCertificate = 64 :=
  Certificates.certificate23100.1

theorem centInvT0_length : centInvT0.length = 1 :=
  Certificates.certificate23100.2

namespace X11

theorem wordXY_mem (w : List Char) : wordXY w ∈ QP45.originalSubgroup := by
  have hx : x45 ∈ QP45.originalSubgroup := by rw [QP45_closure]; exact subset_closure (by simp)
  have hy : y45 ∈ QP45.originalSubgroup := by rw [QP45_closure]; exact subset_closure (by simp)
  have key : ∀ (w : List Char) (g : Equiv.Perm (Fin 45)), g ∈ QP45.originalSubgroup →
      w.foldl (fun g c => g * if c = 'x' then x45 else y45) g ∈ QP45.originalSubgroup := by
    intro w
    induction w with
    | nil => exact fun g hg => hg
    | cons c w ih =>
      intro g hg
      refine ih _ (mul_mem hg ?_)
      split_ifs
      exacts [hx, hy]
  exact key w 1 (one_mem _)

theorem QT0_le : QT0.originalSubgroup ≤ QP45.originalSubgroup := by
  rw [QT0, certificate_originalSubgroup, closure_le]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
  rcases hg with rfl | rfl | rfl <;> rw [tab_eq]
  exacts [wordXY_mem _, wordXY_mem _, wordXY_mem _]

end X11

namespace X11

theorem mem_invT0 {g : Equiv.Perm (Fin 45)} :
    g ∈ invT0 ↔ g ∈ elemsT QT0 ∧ g * g = 1 ∧ g ≠ 1 := by
  unfold invT0
  rw [List.mem_filter]
  simp only [Bool.and_eq_true, decide_eq_true_eq]

theorem mem_centInvT0 {g : Equiv.Perm (Fin 45)} :
    g ∈ centInvT0 ↔ g ∈ invT0 ∧ ∀ t ∈ invT0, g * t = t * g := by
  unfold centInvT0
  rw [List.mem_filter, List.all_eq_true]
  simp only [decide_eq_true_eq]

end X11

theorem sp43_eq_of_comm_inv
    {Y : Type} [Group Y] [Finite Y] (hY : Blueprint.LieModel Y .PSp 2 3 1) (T : Sylow 2 Y)
    {s s' : Y} (hs : s ∈ (T : Subgroup Y)) (hs' : s' ∈ (T : Subgroup Y))
    (hs2 : s * s = 1) (hs1 : s ≠ 1) (hs'2 : s' * s' = 1) (hs'1 : s' ≠ 1)
    (hc : ∀ t ∈ (T : Subgroup Y), t * t = 1 → t ≠ 1 → s * t = t * s ∧ s' * t = t * s') :
    s = s' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := equiv_of_lieModel hY
  have hQT0 : ValidSchreier QT0 := QT0_valid.1
  set P : Subgroup (Equiv.Perm (Fin 45)) := QP45.originalSubgroup with hP
  have hcT0 : Nat.card QT0.originalSubgroup = 64 :=
    (card_group QT0 hQT0).trans QT0_valid.2
  have hcP : Nat.card P = 25920 := (card_group QP45 QP45_ok).trans QP45_valid.2
  set T0' : Subgroup ↥P := QT0.originalSubgroup.subgroupOf P with hT0'
  have hcT0' : Nat.card T0' = 64 := by
    rw [hT0', Nat.card_congr (subgroupOfEquivOfLe X11.QT0_le).toEquiv, hcT0]
  have h2 : IsPGroup 2 T0' := IsPGroup.of_card (n := 6) (by rw [hcT0']; norm_num)
  have hidx : ¬ 2 ∣ T0'.index := by
    have h1 := T0'.card_mul_index
    rw [hcT0', hcP] at h1
    intro h3
    obtain ⟨k, hk⟩ := h3
    omega
  set S0 : Sylow 2 ↥P := h2.toSylow hidx with hS0'
  have hsurj : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, by simp⟩
  set TP : Sylow 2 ↥P := T.mapSurjective hsurj with hTP'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥P) S0 TP
  have hTP : ∀ y : ↥P, y ∈ (TP : Subgroup ↥P) ↔ e.symm y ∈ (T : Subgroup Y) := by
    intro y
    rw [hTP', Sylow.coe_mapSurjective]
    constructor
    · rintro ⟨y₀, hy₀, rfl⟩
      have h1 : e.symm (e.toMonoidHom y₀) = y₀ := e.symm_apply_apply y₀
      rw [h1]
      exact hy₀
    · intro hy
      exact ⟨e.symm y, hy, by simp⟩
  have hS0 : ∀ y : ↥P, y ∈ (S0 : Subgroup ↥P) ↔
      (y : Equiv.Perm (Fin 45)) ∈ QT0.originalSubgroup := fun y => by
    rw [hS0', IsPGroup.toSylow_coe, hT0', mem_subgroupOf]
  have hconj : ∀ y : ↥P, y ∈ (TP : Subgroup ↥P) ↔ g⁻¹ * y * g ∈ (S0 : Subgroup ↥P) := by
    intro y
    rw [← hg]
    exact CFSG.GH74.GLS.Bg.Thompson.mem_smul_sylow S0 g y
  have hσT : ∀ y ∈ (T : Subgroup Y),
      ((g⁻¹ * e y * g : ↥P) : Equiv.Perm (Fin 45)) ∈ QT0.originalSubgroup := fun y hy =>
    (hS0 _).mp ((hconj _).mp ((hTP _).mpr (by simpa using hy)))
  have hσinj : ∀ y y' : Y, ((g⁻¹ * e y * g : ↥P) : Equiv.Perm (Fin 45)) =
      ((g⁻¹ * e y' * g : ↥P) : Equiv.Perm (Fin 45)) → y = y' := by
    intro y y' h
    have h1 : (g⁻¹ * e y * g : ↥P) = g⁻¹ * e y' * g := Subtype.ext h
    have h3 : e y = e y' := by
      calc e y = g * (g⁻¹ * e y * g) * g⁻¹ := by group
        _ = g * (g⁻¹ * e y' * g) * g⁻¹ := by rw [h1]
        _ = e y' := by group
    exact e.injective h3
  have hσsurj : ∀ t ∈ invT0, ∃ y₀ ∈ (T : Subgroup Y), y₀ * y₀ = 1 ∧ y₀ ≠ 1 ∧
      ((g⁻¹ * e y₀ * g : ↥P) : Equiv.Perm (Fin 45)) = t := by
    intro t ht
    obtain ⟨htE, ht2, ht1⟩ := X11.mem_invT0.mp ht
    have htQ := (mem_elemsT QT0 hQT0 t).mp htE
    set t' : ↥P := ⟨t, X11.QT0_le htQ⟩ with ht'
    have ht'S : g⁻¹ * (g * t' * g⁻¹) * g ∈ (S0 : Subgroup ↥P) := by
      rw [show g⁻¹ * (g * t' * g⁻¹) * g = t' by group, hS0]
      exact htQ
    have hmem := (hTP _).mp ((hconj _).mpr ht'S)
    have ht'2 : t' * t' = 1 := Subtype.ext ht2
    refine ⟨e.symm (g * t' * g⁻¹), hmem, ?_, ?_, ?_⟩
    · rw [← map_mul, show g * t' * g⁻¹ * (g * t' * g⁻¹) = g * (t' * t') * g⁻¹ by group, ht'2,
        mul_one, mul_inv_cancel, map_one]
    · intro h1
      apply ht1
      have h3 : g * t' * g⁻¹ = 1 := by
        have := congrArg e h1
        rwa [MulEquiv.apply_symm_apply, map_one] at this
      have h4 : t' = 1 := by
        calc t' = g⁻¹ * (g * t' * g⁻¹) * g := by group
          _ = 1 := by rw [h3]; group
      exact congrArg Subtype.val h4
    · rw [MulEquiv.apply_symm_apply, show g⁻¹ * (g * t' * g⁻¹) * g = t' by group]
  have key : ∀ y ∈ (T : Subgroup Y), y * y = 1 → y ≠ 1 →
      (∀ t ∈ (T : Subgroup Y), t * t = 1 → t ≠ 1 → y * t = t * y) →
      ((g⁻¹ * e y * g : ↥P) : Equiv.Perm (Fin 45)) ∈ centInvT0 := by
    intro y hy hy2 hy1 hyc
    have hsq : (g⁻¹ * e y * g * (g⁻¹ * e y * g) : ↥P) = 1 := by
      calc (g⁻¹ * e y * g * (g⁻¹ * e y * g) : ↥P) = g⁻¹ * (e y * e y) * g := by group
        _ = g⁻¹ * e (y * y) * g := by rw [map_mul]
        _ = 1 := by rw [hy2, map_one, mul_one, inv_mul_cancel]
    have hinv : ((g⁻¹ * e y * g : ↥P) : Equiv.Perm (Fin 45)) ∈ invT0 := by
      refine X11.mem_invT0.mpr ⟨(mem_elemsT QT0 hQT0 _).mpr (hσT y hy), ?_, ?_⟩
      · exact congrArg Subtype.val hsq
      · intro h1
        apply hy1
        apply hσinj
        rw [h1, map_one, mul_one, inv_mul_cancel]
        rfl
    refine X11.mem_centInvT0.mpr ⟨hinv, fun t ht => ?_⟩
    obtain ⟨y₀, hy₀, hy₀2, hy₀1, rfl⟩ := hσsurj t ht
    have h1 := hyc y₀ hy₀ hy₀2 hy₀1
    have hAB : (g⁻¹ * e y * g * (g⁻¹ * e y₀ * g) : ↥P) = g⁻¹ * e y₀ * g * (g⁻¹ * e y * g) := by
      calc (g⁻¹ * e y * g * (g⁻¹ * e y₀ * g) : ↥P) = g⁻¹ * (e y * e y₀) * g := by group
        _ = g⁻¹ * e (y * y₀) * g := by rw [map_mul]
        _ = g⁻¹ * e (y₀ * y) * g := by rw [h1]
        _ = g⁻¹ * (e y₀ * e y) * g := by rw [map_mul]
        _ = g⁻¹ * e y₀ * g * (g⁻¹ * e y * g) := by group
    exact congrArg Subtype.val hAB
  obtain ⟨c, hc1⟩ := List.length_eq_one_iff.mp centInvT0_length
  have h1 := key s hs hs2 hs1 (fun t ht ht2 ht1 => (hc t ht ht2 ht1).1)
  have h2 := key s' hs' hs'2 hs'1 (fun t ht ht2 ht1 => (hc t ht ht2 ht1).2)
  rw [hc1, List.mem_singleton] at h1 h2
  exact hσinj s s' (h1.trans h2.symm)

namespace X11

theorem psp4_conj_of_not_conj {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hY : Blueprint.LieModel Y .PSp 2 p f) {t t' w : Y} (ht : orderOf t = 2)
    (ht' : orderOf t' = 2) (hw : orderOf w = 2) (hn : ∀ g : Y, g⁻¹ * t * g ≠ t') :
    (∃ g : Y, g⁻¹ * t * g = w) ∨ ∃ g : Y, g⁻¹ * t' * g = w := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hY
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  have hcls : ∀ u : Y, orderOf u = 2 → ∃ g : Y,
      g⁻¹ * u * g = e.symm (CatFactsSp4.u1 K) ∨ g⁻¹ * u * g = e.symm (CatFactsSp4.u2 K) := by
    intro u hu
    obtain ⟨g, hg⟩ := CatFactsSp4.exists_conj_of_orderOf_eq_two hodd
      (by rw [MulEquiv.orderOf_eq, hu] : orderOf (e u) = 2)
    refine ⟨e.symm g, ?_⟩
    rcases hg with hg | hg
    · left
      apply e.injective
      simp [hg]
    · right
      apply e.injective
      simp [hg]
  have hsymm : ∀ u u' : Y, (∃ g : Y, g⁻¹ * u * g = u') → ∃ g : Y, g⁻¹ * u' * g = u := by
    rintro u u' ⟨g, rfl⟩
    exact ⟨g⁻¹, by group⟩
  have htrans : ∀ u u' u'' : Y, (∃ g : Y, g⁻¹ * u * g = u') → (∃ g : Y, g⁻¹ * u' * g = u'') →
      ∃ g : Y, g⁻¹ * u * g = u'' := by
    rintro u u' u'' ⟨g, rfl⟩ ⟨g', rfl⟩
    exact ⟨g * g', by group⟩
  obtain ⟨g₁, hg₁⟩ := hcls t ht
  obtain ⟨g₂, hg₂⟩ := hcls t' ht'
  obtain ⟨g₃, hg₃⟩ := hcls w hw
  have hnc : ¬ ∃ g : Y, g⁻¹ * t * g = t' := fun ⟨g, hg⟩ => hn g hg
  rcases hg₁ with h1 | h1 <;> rcases hg₂ with h2 | h2 <;> rcases hg₃ with h3 | h3
  · exact (hnc (htrans _ _ _ ⟨g₁, h1⟩ (hsymm _ _ ⟨g₂, h2⟩))).elim
  · exact (hnc (htrans _ _ _ ⟨g₁, h1⟩ (hsymm _ _ ⟨g₂, h2⟩))).elim
  · exact Or.inl (htrans _ _ _ ⟨g₁, h1⟩ (hsymm _ _ ⟨g₃, h3⟩))
  · exact Or.inr (htrans _ _ _ ⟨g₂, h2⟩ (hsymm _ _ ⟨g₃, h3⟩))
  · exact Or.inr (htrans _ _ _ ⟨g₂, h2⟩ (hsymm _ _ ⟨g₃, h3⟩))
  · exact Or.inl (htrans _ _ _ ⟨g₁, h1⟩ (hsymm _ _ ⟨g₃, h3⟩))
  · exact (hnc (htrans _ _ _ ⟨g₁, h1⟩ (hsymm _ _ ⟨g₂, h2⟩))).elim
  · exact (hnc (htrans _ _ _ ⟨g₁, h1⟩ (hsymm _ _ ⟨g₂, h2⟩))).elim

theorem exists_conj_of_mk_conj {L : Type*} [Group L] [Finite L] {u u' g : L}
    (hu : u * u = 1) (hu' : u' * u' = 1)
    (hg : (QuotientGroup.mk (g⁻¹ * u * g) : L ⧸ pPrimeCore 2 L) = QuotientGroup.mk u') :
    ∃ h : L, h⁻¹ * u * h = u' := by
  set v := g⁻¹ * u * g with hv
  have hv2 : v * v = 1 := by
    rw [hv, show g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group, hu]
    group
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  set o := v * u' with ho
  clear_value o v
  have hoO : o ∈ pPrimeCore 2 L := by
    rw [ho]
    have := QuotientGroup.eq.mp hg
    rwa [hvinv] at this
  have hodd : Odd (orderOf o) := by
    have h1 := orderOf_dvd_natCard (⟨o, hoO⟩ : ↥(pPrimeCore 2 L))
    rw [Subgroup.orderOf_mk] at h1
    have h2 : ¬ 2 ∣ Nat.card (pPrimeCore 2 L) :=
      (Nat.prime_two.coprime_iff_not_dvd).mp (pPrimeCore_coprime_card (p := 2) (G := L))
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    exact fun h3 => h2 (h3.trans h1)
  have hinv : ∀ k : ℕ, v * o ^ k * v = (o ^ k)⁻¹ := by
    intro k
    have h1 : v * o * v = o⁻¹ := by
      rw [ho, mul_inv_rev, inv_eq_of_mul_eq_one_right hu', hvinv]
      calc v * (v * u') * v = (v * v) * u' * v := by group
        _ = u' * v := by rw [hv2, one_mul]
    have h2 : v * o ^ k * v = (v * o * v) ^ k := by
      have hvv : v⁻¹ = v := hvinv
      calc v * o ^ k * v = v * o ^ k * v⁻¹ := by rw [hvv]
        _ = (v * o * v⁻¹) ^ k := (conj_pow).symm
        _ = (v * o * v) ^ k := by rw [hvv]
    rw [h2, h1, inv_pow]
  obtain ⟨m, hm⟩ := hodd
  refine ⟨g * o ^ (m + 1), ?_⟩
  have hpow : o ^ (m + 1) * o ^ (m + 1) = o := by
    rw [← pow_add, show m + 1 + (m + 1) = orderOf o + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have h3 : v * (o ^ (m + 1))⁻¹ * v = o ^ (m + 1) := by
    calc v * (o ^ (m + 1))⁻¹ * v = v * (v * o ^ (m + 1) * v) * v := by rw [hinv (m + 1)]
      _ = (v * v) * o ^ (m + 1) * (v * v) := by group
      _ = o ^ (m + 1) := by rw [hv2, one_mul, mul_one]
  calc (g * o ^ (m + 1))⁻¹ * u * (g * o ^ (m + 1)) = (o ^ (m + 1))⁻¹ * v * o ^ (m + 1) := by
        rw [hv]; group
    _ = v * (v * (o ^ (m + 1))⁻¹ * v) * o ^ (m + 1) := by
        rw [show v * (v * (o ^ (m + 1))⁻¹ * v) = (v * v) * (o ^ (m + 1))⁻¹ * v by group, hv2,
          one_mul]
    _ = v * (o ^ (m + 1) * o ^ (m + 1)) := by rw [h3, mul_assoc]
    _ = u' := by rw [hpow, ho, ← mul_assoc, hv2, one_mul]

end X11

end CFSG.ComponentClassification.GSThmB
