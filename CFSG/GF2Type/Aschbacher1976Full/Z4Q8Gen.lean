module

public import CFSG.GF2Type.Aschbacher1976Full.Z4Q8Order
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25
public import CFSG.GF2Type.Aschbacher1976Common.DihedralEvenRank

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Z4Q8

open CFSG CFSG.Blueprint CFSG.EvenSporadicStandard.Finkelstein77
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_Zc_iff {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {x : G} :
    x ∈ Zc z ↔ x ∈ Fz z ∧ ∀ f ∈ Fz z, x * f = f * x := by
  constructor
  · intro hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨w.2, fun f hf => ?_⟩
    have h := Subgroup.mem_center_iff.mp hw ⟨f, hf⟩
    exact (congrArg Subtype.val h).symm
  · rintro ⟨hxF, hc⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxF⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hc g.1 g.2).symm

theorem comm_z_Fz {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {f : G} (hf : f ∈ Fz z) :
    f * z = z * f := by
  have hzc : z ∈ Zc z := z_mem_Zc hZ hz
  exact ((mem_Zc_iff hZ hz).mp hzc).2 f hf |>.symm

theorem conj_mem_Fz {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {h : G} (hh : h ∈ Hz z)
    {x : G} (hx : x ∈ Fz z) : h * x * h⁻¹ ∈ Fz z := by
  have hN : (generalizedFitting ↥(Hz z)).Normal := by
    rw [generalizedFitting_Hz_eq_pCore hZ hz]
    exact pCore_normal
  have hx' : x ∈ (generalizedFitting ↥(Hz z)).map (Hz z).subtype := hx
  obtain ⟨x', hx'g, rfl⟩ := Subgroup.mem_map.mp hx'
  have key : (⟨h, hh⟩ : ↥(Hz z)) * x' * (⟨h, hh⟩ : ↥(Hz z))⁻¹ ∈ generalizedFitting ↥(Hz z) :=
    hN.conj_mem x' hx'g ⟨h, hh⟩
  have hval : (Hz z).subtype ((⟨h, hh⟩ : ↥(Hz z)) * x' * (⟨h, hh⟩ : ↥(Hz z))⁻¹) ∈
      (generalizedFitting ↥(Hz z)).map (Hz z).subtype := Subgroup.mem_map_of_mem _ key
  have e : (Hz z).subtype ((⟨h, hh⟩ : ↥(Hz z)) * x' * (⟨h, hh⟩ : ↥(Hz z))⁻¹) =
      h * (Hz z).subtype x' * h⁻¹ := by
    simp
  rw [e] at hval
  exact hval

theorem conj_mem_Zc {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {h : G} (hh : h ∈ Hz z)
    {x : G} (hx : x ∈ Zc z) : h * x * h⁻¹ ∈ Zc z := by
  obtain ⟨hxF, hc⟩ := (mem_Zc_iff hZ hz).mp hx
  rw [mem_Zc_iff hZ hz]
  refine ⟨conj_mem_Fz hZ hz hh hxF, fun f hf => ?_⟩
  have hf' : h⁻¹ * f * h⁻¹⁻¹ ∈ Fz z := conj_mem_Fz hZ hz (Subgroup.inv_mem _ hh) hf
  have hc' := hc (h⁻¹ * f * h⁻¹⁻¹) hf'
  calc h * x * h⁻¹ * f = h * (x * (h⁻¹ * f * h⁻¹⁻¹)) * h⁻¹ := by group
    _ = h * ((h⁻¹ * f * h⁻¹⁻¹) * x) * h⁻¹ := by rw [hc']
    _ = f * (h * x * h⁻¹) := by group

theorem mem_Hz_of_conj_mem_Zc {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {h : G}
    (hh : h * z * h⁻¹ ∈ Zc z) : h ∈ Hz z := by
  obtain ⟨Z, A, hZeq, hcyc, -⟩ := unpack hZ hz
  have hcycZc : IsCyclic ↥(Zc z) := by rw [hZeq]; exact hcyc
  have hsq : (h * z * h⁻¹) ^ 2 = 1 := by
    have h2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    calc (h * z * h⁻¹) ^ 2 = h * (z * z) * h⁻¹ := by rw [sq]; group
      _ = h * z ^ 2 * h⁻¹ := by rw [sq]
      _ = 1 := by rw [h2]; group
  rcases involution_eq_one_or_eq hcycZc hz (z_mem_Zc hZ hz) hh hsq with h1 | h1
  · exfalso
    have : z = 1 := by
      calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.mp hw]
    have h3 : h * z = z * h := by
      have := h1
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    exact h3.symm

theorem normalizer_Zc_le_Hz {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {h : G}
    (hh : h ∈ Subgroup.normalizer (Zc z : Set G)) : h ∈ Hz z := by
  apply mem_Hz_of_conj_mem_Zc hZ hz
  have hzZ := z_mem_Zc hZ hz
  exact (Subgroup.mem_normalizer_iff.mp hh z).mp hzZ

theorem closure_pair_ne_Fz {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {a b : G}
    (ha : a ∈ Fz z) (hb : b ∈ Fz z) : Subgroup.closure ({a, b} : Set G) ≠ Fz z := by
  classical
  intro hcl
  have hzF : z ∈ Fz z := (mem_Zc_iff hZ hz).mp (z_mem_Zc hZ hz) |>.1
  have hcentN : ∀ n ∈ Subgroup.zpowers z, ∀ g ∈ Fz z, g * n = n * g := by
    intro n hn g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact ((show Commute g z from comm_z_Fz hZ hz hg).zpow_right k).eq
  have hNF : ∀ n ∈ Subgroup.zpowers z, n ∈ Fz z := fun n hn =>
    (Subgroup.zpowers_le.mpr hzF) hn
  have ha2 : a ^ 2 ∈ Subgroup.zpowers z := sq_mem_zpowers_Fz hZ hz ha
  have hb2 : b ^ 2 ∈ Subgroup.zpowers z := sq_mem_zpowers_Fz hZ hz hb
  have hab2 : (a * b) ^ 2 ∈ Subgroup.zpowers z := sq_mem_zpowers_Fz hZ hz (Fz z |>.mul_mem ha hb)
  have hc : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z := comm_mem_zpowers_Fz hZ hz ha hb
  set c := a * b * a⁻¹ * b⁻¹ with hcdef
  have hca : a * c = c * a := hcentN c hc a ha
  have hcb : b * c = c * b := hcentN c hc b hb
  have hcab : c * (a * b) = a * b * c := by
    calc c * (a * b) = (c * a) * b := by group
      _ = (a * c) * b := by rw [← hca]
      _ = a * (c * b) := by group
      _ = a * (b * c) := by rw [← hcb]
      _ = a * b * c := by group
  have hba : b * a = a * b * c⁻¹ := by
    calc b * a = c⁻¹ * (a * b) := by rw [hcdef]; group
      _ = c⁻¹ * (a * b * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * (a * b)) * c⁻¹ := by rw [hcab]
      _ = a * b * c⁻¹ := by group
  have hba2 : b * a ^ 2 = a ^ 2 * b := hcentN (a ^ 2) ha2 b hb
  let P : G → Prop := fun x => x ∈ Fz z ∧ ∃ n ∈ Subgroup.zpowers z,
    x = n ∨ x = a * n ∨ x = b * n ∨ x = a * b * n
  have hPN : ∀ x, P x → ∀ m ∈ Subgroup.zpowers z, P (x * m) := by
    rintro x ⟨hxF, n, hn, h⟩ m hm
    refine ⟨Fz z |>.mul_mem hxF (hNF m hm), n * m, Subgroup.mul_mem _ hn hm, ?_⟩
    rcases h with h | h | h | h <;> rw [h]
    · exact Or.inl (by group)
    · exact Or.inr (Or.inl (by group))
    · exact Or.inr (Or.inr (Or.inl (by group)))
    · exact Or.inr (Or.inr (Or.inr (by group)))
  have hPa : ∀ x, P x → P (x * a) := by
    rintro x ⟨hxF, n, hn, h⟩
    refine ⟨Fz z |>.mul_mem hxF ha, ?_⟩
    rcases h with h | h | h | h <;> rw [h]
    · exact ⟨n, hn, Or.inr (Or.inl (hcentN n hn a ha).symm)⟩
    · refine ⟨a ^ 2 * n, Subgroup.mul_mem _ ha2 hn, Or.inl ?_⟩
      calc a * n * a = a * (n * a) := by group
        _ = a * (a * n) := by rw [(hcentN n hn a ha).symm]
        _ = a ^ 2 * n := by rw [sq]; group
    · refine ⟨c⁻¹ * n, Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hn, Or.inr (Or.inr (Or.inr ?_))⟩
      calc b * n * a = b * (n * a) := by group
        _ = b * (a * n) := by rw [(hcentN n hn a ha).symm]
        _ = (b * a) * n := by group
        _ = (a * b * c⁻¹) * n := by rw [hba]
        _ = a * b * (c⁻¹ * n) := by group
    · refine ⟨a ^ 2 * (c⁻¹ * n), Subgroup.mul_mem _ ha2 (Subgroup.mul_mem _
        (Subgroup.inv_mem _ hc) hn), Or.inr (Or.inr (Or.inl ?_))⟩
      calc a * b * n * a = a * b * (n * a) := by group
        _ = a * b * (a * n) := by rw [(hcentN n hn a ha).symm]
        _ = a * (b * a) * n := by group
        _ = a * (a * b * c⁻¹) * n := by rw [hba]
        _ = a ^ 2 * b * (c⁻¹ * n) := by rw [sq]; group
        _ = (b * a ^ 2) * (c⁻¹ * n) := by rw [hba2]
        _ = b * (a ^ 2 * (c⁻¹ * n)) := by group
  have hPb : ∀ x, P x → P (x * b) := by
    rintro x ⟨hxF, n, hn, h⟩
    refine ⟨Fz z |>.mul_mem hxF hb, ?_⟩
    rcases h with h | h | h | h <;> rw [h]
    · exact ⟨n, hn, Or.inr (Or.inr (Or.inl (hcentN n hn b hb).symm))⟩
    · exact ⟨n, hn, Or.inr (Or.inr (Or.inr (by
        calc a * n * b = a * (n * b) := by group
          _ = a * (b * n) := by rw [(hcentN n hn b hb).symm]
          _ = a * b * n := by group)))⟩
    · refine ⟨b ^ 2 * n, Subgroup.mul_mem _ hb2 hn, Or.inl ?_⟩
      calc b * n * b = b * (n * b) := by group
        _ = b * (b * n) := by rw [(hcentN n hn b hb).symm]
        _ = b ^ 2 * n := by rw [sq]; group
    · refine ⟨b ^ 2 * n, Subgroup.mul_mem _ hb2 hn, Or.inr (Or.inl ?_)⟩
      calc a * b * n * b = a * (b * n * b) := by group
        _ = a * (b * (n * b)) := by group
        _ = a * (b * (b * n)) := by rw [(hcentN n hn b hb).symm]
        _ = a * (b ^ 2 * n) := by rw [sq]; group
  have hPainv : ∀ x, P x → P (x * a⁻¹) := by
    intro x hx
    have e : x * a⁻¹ = (x * a) * (a ^ 2)⁻¹ := by rw [sq]; group
    rw [e]
    exact hPN _ (hPa x hx) _ (Subgroup.inv_mem _ ha2)
  have hPbinv : ∀ x, P x → P (x * b⁻¹) := by
    intro x hx
    have e : x * b⁻¹ = (x * b) * (b ^ 2)⁻¹ := by rw [sq]; group
    rw [e]
    exact hPN _ (hPb x hx) _ (Subgroup.inv_mem _ hb2)
  have hall : ∀ x ∈ Subgroup.closure ({a, b} : Set G), P x := by
    intro x hx
    refine Subgroup.closure_induction_right (p := fun x _ => P x) ?_ ?_ ?_ hx
    · exact ⟨Fz z |>.one_mem, 1, Subgroup.one_mem _, Or.inl rfl⟩
    · intro x hx y hy hPx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hPa x hPx
      · exact hPb x hPx
    · intro x hx y hy hPx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hPainv x hPx
      · exact hPbinv x hPx
  let S8 : Finset G := {1, a, b, a * b, z, a * z, b * z, a * b * z}
  have hsub : (Fz z : Set G) ⊆ (S8 : Set G) := by
    intro x hxF
    rw [← hcl] at hxF
    obtain ⟨-, n, hn, h⟩ := hall x hxF
    have hn' : n = 1 ∨ n = z := mem_zpowers_two hz hn
    rcases h with h | h | h | h <;> rcases hn' with hn' | hn' <;> rw [h, hn'] <;> simp [S8]
  have hS8card : S8.card ≤ 8 := by
    have h1 : S8 = [1, a, b, a * b, z, a * z, b * z, a * b * z].toFinset := by
      ext x
      simp [S8]
    rw [h1]
    exact (List.toFinset_card_le _).trans (by simp)
  have hF8 : (Fz z : Set G).ncard ≤ 8 := by
    calc (Fz z : Set G).ncard ≤ (S8 : Set G).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = S8.card := Set.ncard_coe_finset _
      _ ≤ 8 := hS8card
  have hF16 := card_Fz hZ hz
  have hcoe : Nat.card ↥(Fz z) = (Fz z : Set G).ncard := Nat.card_coe_set_eq _
  omega

theorem mem_conjugate_iff' {A : Subgroup G} {g x : G} :
    x ∈ conjugate A g ↔ g * x * g⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    show g * (g⁻¹ * a * g⁻¹⁻¹) * g⁻¹ ∈ A
    have e : g * (g⁻¹ * a * g⁻¹⁻¹) * g⁻¹ = a := by group
    rw [e]
    exact ha
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp; group⟩

theorem conjugate_Zc_eq {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {g : G}
    (hg : g ∈ Hz z) : conjugate (Zc z) g = Zc z := by
  ext x
  rw [mem_conjugate_iff']
  constructor
  · intro hx
    have h := conj_mem_Zc hZ hz (Subgroup.inv_mem _ hg) hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e] at h
    exact h
  · intro hx
    exact conj_mem_Zc hZ hz hg hx

theorem card_Zc {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) : Nat.card ↥(Zc z) = 4 := by
  obtain ⟨Z, A, hZeq, -, hZ4, -⟩ := unpack hZ hz
  rw [hZeq, hZ4]

theorem TI_Zc {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) (g : G) :
    conjugate (Zc z) g = Zc z ∨ Zc z ⊓ conjugate (Zc z) g = ⊥ := by
  by_cases hg : conjugate (Zc z) g = Zc z
  · exact Or.inl hg
  right
  have hcycZc : IsCyclic ↥(Zc z) := by
    obtain ⟨Z, A, hZeq, hcyc, -⟩ := unpack hZ hz
    rw [hZeq]
    exact hcyc
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  obtain ⟨hxZ, hxC⟩ := Subgroup.mem_inf.mp hx
  have hx4 : x ^ 4 = 1 := by
    have h := pow_card_eq_one' (x := (⟨x, hxZ⟩ : ↥(Zc z)))
    rw [card_Zc hZ hz] at h
    exact congrArg Subtype.val h
  have hzW : z ∈ conjugate (Zc z) g := by
    have hx2 : x ^ 2 ∈ conjugate (Zc z) g := (conjugate (Zc z) g).pow_mem hxC 2
    have hx2Z : x ^ 2 ∈ Zc z := (Zc z).pow_mem hxZ 2
    have hx2sq : (x ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hx4
    rcases involution_eq_one_or_eq hcycZc hz (z_mem_Zc hZ hz) hx2Z hx2sq with h | h
    · have hx2' : x ^ 2 = 1 := h
      rcases involution_eq_one_or_eq hcycZc hz (z_mem_Zc hZ hz) hxZ hx2' with h' | h'
      · exact absurd h' hx1
      · rw [h'] at hxC
        exact hxC
    · rw [h] at hx2
      exact hx2
  have hgH : g ∈ Hz z := mem_Hz_of_conj_mem_Zc hZ hz (mem_conjugate_iff'.mp hzW)
  exact hg (conjugate_Zc_eq hZ hz hgH)

theorem closure_finset_ne_Fz {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) (s : Finset G)
    (hs : s.card ≤ 2) (hsF : ∀ x ∈ s, x ∈ Fz z) : Subgroup.closure (s : Set G) ≠ Fz z := by
  classical
  have key : ∃ a b : G, a ∈ Fz z ∧ b ∈ Fz z ∧ (s : Set G) ⊆ {a, b} := by
    obtain h | h | h : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
    · exact ⟨1, 1, (Fz z).one_mem, (Fz z).one_mem, by
        rw [Finset.card_eq_zero.mp h]; simp⟩
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
      exact ⟨a, a, hsF a (by simp), hsF a (by simp), by simp⟩
    · obtain ⟨x, y, -, hs2⟩ := Finset.card_eq_two.mp h
      have hx : x ∈ s := by rw [hs2]; simp
      have hy : y ∈ s := by rw [hs2]; simp
      refine ⟨x, y, hsF x hx, hsF y hy, ?_⟩
      intro w hw
      rw [Finset.mem_coe, hs2] at hw
      simpa using hw
  obtain ⟨a, b, ha, hb, hsub⟩ := key
  intro heq
  apply closure_pair_ne_Fz hZ hz ha hb
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · rw [← heq]
    exact Subgroup.closure_mono hsub

theorem exists_conj_le_Hz [IsSimpleGroup G] (hdih : ∀ x : G, orderOf x = 4 →
      WeaklyClosedInNormalizer (Subgroup.zpowers x) →
      CFSG.ComponentClassification.AschbacherKnownGroup.HasDihedralSylowTwo G ∨
        CFSG.ComponentClassification.AschbacherKnownGroup.HasSemidihedralSylowTwo G)
    {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {k : G} (hk : orderOf k = 4)
    (hkZ : Subgroup.zpowers k = Zc z) :
    ∃ h : G, (Zc z).map (MulAut.conj h).toMonoidHom ≤ Hz z ∧
      (Zc z).map (MulAut.conj h).toMonoidHom ≠ Zc z := by
  by_contra hcon
  push Not at hcon
  have hnorm : Subgroup.normalizer (Zc z : Set G) ≤ Hz z := fun x hx =>
    normalizer_Zc_le_Hz hZ hz hx
  have hwc : WeaklyClosedInNormalizer (Subgroup.zpowers k) := by
    rw [hkZ]
    intro h hle
    exact hcon h (hle.trans hnorm)
  have hdk := hdih k hk hwc
  have hP : IsPGroup 2 ↥(Fz z) := IsPGroup.of_card (n := 4) (by rw [card_Fz hZ hz]; norm_num)
  obtain ⟨s, hs, hsF⟩ := CFSG.GF2Type.Aschbacher1976Common.twoGen_of_isPGroup hdk hP
  exact closure_finset_ne_Fz hZ hz s hs (fun x hx => hsF ▸ Subgroup.subset_closure hx) hsF

end CFSG.GF2Type.Aschbacher1976Full.Z4Q8
