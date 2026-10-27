module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Center
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5MComp
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

namespace Case2Data

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

private theorem exists_zpow_of_mem_zOf (h : Case2Data p P T D F x) {w : Y} (hw : w ∈ zOf T)
    (hw1 : w ≠ 1) : ∀ s ∈ zOf T, ∃ m : ℤ, w ^ m = s := by
  haveI := h.fact
  intro s hs
  have h1 : (⟨w, hw⟩ : zOf T) ≠ 1 := fun e => hw1 (congrArg Subtype.val e)
  have := mem_zpowers_of_prime_card h.zOf_card (g' := (⟨s, hs⟩ : zOf T)) h1
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp this
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

private theorem exists_ne_one_zOf (h : Case2Data p P T D F x) : ∃ t ∈ zOf T, t ≠ 1 := by
  haveI := h.fact
  have hc : 1 < Nat.card (zOf T) := by rw [h.zOf_card]; exact h.prime.one_lt
  haveI : Finite (zOf T) := inferInstance
  haveI : Nontrivial (zOf T) := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨⟨t, ht⟩, ht1⟩ := exists_ne (1 : zOf T)
  exact ⟨t, ht, fun e => ht1 (Subtype.ext e)⟩

private theorem mem_map_conj_iff (L : Subgroup Y) (g y : Y) :
    y ∈ L.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ L := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

private theorem center_map_conj_ne_bot {L : Subgroup Y} (g : Y) (hc : center L ≠ ⊥) :
    center (L.map (MulAut.conj g).toMonoidHom) ≠ ⊥ := by
  obtain ⟨⟨⟨a, haL⟩, hac⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc
  have hcomm : ∀ b ∈ L, b * a = a * b := fun b hb =>
    congrArg Subtype.val (mem_center_iff.mp hac ⟨b, hb⟩)
  have hmem : g * a * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := by
    rw [mem_map_conj_iff]
    have e : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    rw [e]
    exact haL
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨⟨g * a * g⁻¹, hmem⟩, ?_⟩, ?_⟩
  · rw [mem_center_iff]
    rintro ⟨b, hb⟩
    apply Subtype.ext
    have hb' : g⁻¹ * b * g ∈ L := (mem_map_conj_iff L g b).mp hb
    have h1 := hcomm _ hb'
    show b * (g * a * g⁻¹) = g * a * g⁻¹ * b
    calc b * (g * a * g⁻¹) = g * ((g⁻¹ * b * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * b * g)) * g⁻¹ := by rw [h1]
      _ = g * a * g⁻¹ * b := by group
  · intro e
    have e1 : g * a * g⁻¹ = 1 := congrArg (fun z => z.1.1) e
    exact ha1 (Subtype.ext (Subtype.ext (conj_eq_one_iff.mp e1)))

theorem exists_central_line (h : Case2Data p P T D F x) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    ∃ t ∈ zOf T, ∃ j : ℕ, t * x ^ j ∈ L ∧ t * x ^ j ≠ 1 := by
  classical
  haveI := h.fact
  have hPn := h.P_le_normalizer hL
  have hpg : IsPGroup p P := by
    obtain ⟨S, hS⟩ := h.sylow
    rw [← hS]
    exact S.isPGroup'
  haveI : Group.IsNilpotent P := hpg.isNilpotent
  obtain ⟨t0, ht0, ht0o, -⟩ := h.exists_mem_P_inf hL
  have hnorm : ((P ⊓ L).subgroupOf P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    refine ⟨?_, ?_⟩
    · exact P.mul_mem (P.mul_mem g.2 hn.1) (P.inv_mem g.2)
    · exact (mem_set_normalizer_iff.mp (hPn g.2) _).mp hn.2
  have hne : (P ⊓ L).subgroupOf P ≠ ⊥ := by
    intro hbot
    have h1 : (⟨t0, ht0.1⟩ : P) ∈ (P ⊓ L).subgroupOf P := mem_subgroupOf.mpr ht0
    rw [hbot, mem_bot] at h1
    have h2 : t0 = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at ht0o
    exact h.prime.one_lt.ne ht0o
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨⟨a, haP⟩, hamem⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hc
  have haL : a ∈ P ⊓ L := mem_subgroupOf.mp hamem.1
  have hacent : ∀ b ∈ P, a * b = b * a := fun b hb => by
    have := mem_center_iff.mp hamem.2 ⟨b, hb⟩
    exact (congrArg Subtype.val this).symm
  have ha1' : a ≠ 1 := fun e => ha1 (Subtype.ext (Subtype.ext e))
  have hnk : ∃ k : ℕ, a ^ (p ^ k) = 1 := h.exists_pow_eq_one a haP
  let k := Nat.find hnk
  have hk : a ^ (p ^ k) = 1 := Nat.find_spec hnk
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0] at hk
    simp at hk
    exact ha1' hk
  obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hmin : a ^ (p ^ k') ≠ 1 := Nat.find_min hnk (by omega)
  set u := a ^ (p ^ k') with hu
  have huP : u ∈ P := P.pow_mem haP _
  have huL : u ∈ L := L.pow_mem haL.2 _
  have hu1 : u ^ p = 1 := by
    rw [hu, ← pow_mul, ← pow_succ]
    rw [hk'] at hk
    exact hk
  have huc : ∀ b ∈ P, u * b = b * u := fun b hb =>
    (Commute.pow_left (show Commute a b from hacent b hb) _).eq
  obtain ⟨t, ht, j, htj⟩ := h.central_form huP huc hu1
  exact ⟨t, ht, j, htj ▸ huL, htj ▸ hmin⟩

theorem exists_stabilizer (h : Case2Data p P T D F x) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    ∃ g ∈ F, g ∈ normalizer (L : Set Y) ∧ ∃ z ∈ zOf T, g * z * g⁻¹ ≠ z := by
  classical
  haveI := h.fact
  have hp5 : 5 ≤ p := h.five
  obtain ⟨t₀, ht₀, ht₀1⟩ := h.exists_ne_one_zOf
  have hex : ∀ i : Fin 4, ∃ f ∈ F, f * t₀ * f⁻¹ = t₀ ^ (i.val + 1) := fun i =>
    h.torus.onto t₀ ht₀ (i.val + 1) (fun hd => by
      have h1 := Nat.le_of_dvd (by omega) hd
      have h2 := i.2
      omega)
  choose f hfF hft using hex
  let K : Fin 4 → Subgroup Y := fun i => L.map (MulAut.conj (f i)).toMonoidHom
  have hK : ∀ i, IsComponentOf (K i) ⊤ := fun i =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (f i)) L).mpr hL
  have hnotinj : ¬ Function.Injective K := by
    intro hinj
    have hcard := CFSG.LocalAnalysis.RankThreeTheoremC.card_le_pRank_of_isComponentOf h.prime
      (by omega) h.core (Finset.univ.image K) (fun K' hK' => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hK'
        exact hK i)
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard
    have hrank := h.rank
    omega
  obtain ⟨i, j, hij, hKij⟩ : ∃ i j : Fin 4, i < j ∧ K i = K j := by
    obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hnotinj
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨a, b, hlt, hab⟩
    · exact ⟨b, a, hlt, hab.symm⟩
  have hij' : i.val < j.val := hij
  have hj4 := j.2
  refine ⟨(f i)⁻¹ * f j, F.mul_mem (F.inv_mem (hfF i)) (hfF j), ?_, t₀, ht₀, ?_⟩
  · rw [mem_set_normalizer_iff]
    intro y
    have h1 : ∀ y, (f i)⁻¹ * y * f i ∈ L ↔ (f j)⁻¹ * y * f j ∈ L := fun y => by
      rw [← mem_map_conj_iff, ← mem_map_conj_iff]
      exact Iff.of_eq (congrArg (fun S : Subgroup Y => y ∈ S) hKij)
    have h2 := h1 (f j * y * (f j)⁻¹)
    have e1 : (f j)⁻¹ * (f j * y * (f j)⁻¹) * f j = y := by group
    have e2 : (f i)⁻¹ * (f j * y * (f j)⁻¹) * f i
        = ((f i)⁻¹ * f j) * y * ((f i)⁻¹ * f j)⁻¹ := by group
    rw [e1, e2] at h2
    exact h2.symm
  · intro hfix
    set a := f i with ha
    set b := f j with hb
    have hfa : a * t₀ * a⁻¹ = t₀ ^ (i.val + 1) := hft i
    have hfb : b * t₀ * b⁻¹ = t₀ ^ (j.val + 1) := hft j
    set s := a⁻¹ * t₀ * a with hs
    have hsT : s ∈ T := by
      have := h.torus.F_T a⁻¹ (F.inv_mem (hfF i)) t₀ (h.zOf_le ht₀)
      simpa [hs] using this
    have hsm : s ^ (i.val + 1) = t₀ := by
      have e : s ^ (i.val + 1) = a⁻¹ * t₀ ^ (i.val + 1) * a := by
        simpa [hs] using (conj_pow (a := a⁻¹) (b := t₀) (i := i.val + 1))
      rw [e, ← hfa]
      group
    have hsn : s ^ (j.val + 1) = (a⁻¹ * b) * t₀ * (a⁻¹ * b)⁻¹ := by
      have e : s ^ (j.val + 1) = a⁻¹ * t₀ ^ (j.val + 1) * a := by
        simpa [hs] using (conj_pow (a := a⁻¹) (b := t₀) (i := j.val + 1))
      rw [e, ← hfb]
      group
    have hs1 : s ≠ 1 := by
      intro e
      rw [e, one_pow] at hsm
      exact ht₀1 hsm.symm
    have hsord : orderOf s = p := orderOf_eq_prime (h.pdata.T_exp s hsT) hs1
    have heq : s ^ (j.val + 1) = s ^ (i.val + 1) := by rw [hsn, hfix, hsm]
    rw [pow_eq_pow_iff_modEq, hsord] at heq
    unfold Nat.ModEq at heq
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
    omega

theorem F_mem_normalizer (h : Case2Data p P T D F x) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    {f : Y} (hf : f ∈ F) : f ∈ normalizer (L : Set Y) := by
  classical
  haveI := h.fact
  by_contra hfN
  set L' : Subgroup Y := L.map (MulAut.conj f).toMonoidHom with hL'def
  have hL' : IsComponentOf L' ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj f) L).mpr hL
  have hmem' : ∀ y, y ∈ L' ↔ f⁻¹ * y * f ∈ L := fun y => mem_map_conj_iff L f y
  have hne : L ≠ L' := by
    intro e
    apply hfN
    rw [mem_set_normalizer_iff'']
    intro y
    exact (Iff.of_eq (congrArg (fun S : Subgroup Y => y ∈ S) e)).trans (hmem' y)
  have hLL : ⁅L, L'⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' hL hL' hne
  have hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hLL ha) b hb).symm
  have hZL : center L = ⊥ := by
    by_contra hc
    exact hne (h.eq_of_center_ne_bot hL hL' hc (center_map_conj_ne_bot f hc))
  have hinf : ∀ w, w ∈ L → w ∈ L' → w = 1 := fun w hwL hwL' =>
    CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5MComp.eq_one_of_mem_of_mem_centralizer
      hZL hwL (mem_centralizer_iff.mpr fun g hg => hcomm g hg w hwL')
  obtain ⟨t, ht, j, huL, hu1⟩ := h.exists_central_line hL
  have hxj : x ^ j ∈ D := D.pow_mem h.pdata.x_mem j
  have ht1 : t ≠ 1 := by
    intro e
    subst e
    rw [one_mul] at huL hu1
    have hfinv : f⁻¹ * x ^ j * f = x ^ j := by
      have := h.F_D f⁻¹ (F.inv_mem hf) (x ^ j) hxj
      simpa using this
    exact hu1 (hinf _ huL ((hmem' _).mpr (by rw [hfinv]; exact huL)))
  obtain ⟨g, hgF, hgN, z, hz, hgz⟩ := h.exists_stabilizer hL
  have hgt : g * t * g⁻¹ ≠ t := by
    intro e
    apply hgz
    obtain ⟨m, hm⟩ := h.exists_zpow_of_mem_zOf ht ht1 z hz
    rw [← hm, ← conj_zpow, e]
  have hgx : g * x ^ j * g⁻¹ = x ^ j := h.F_D g hgF _ hxj
  have hw : (g * t * g⁻¹) * t⁻¹ = (g * (t * x ^ j) * g⁻¹) * (t * x ^ j)⁻¹ := by
    have key : g * (t * x ^ j) * g⁻¹ = (g * t * g⁻¹) * x ^ j := by
      calc g * (t * x ^ j) * g⁻¹ = (g * t * g⁻¹) * (g * x ^ j * g⁻¹) := by group
        _ = (g * t * g⁻¹) * x ^ j := by rw [hgx]
    rw [key]
    group
  have hwL : (g * t * g⁻¹) * t⁻¹ ∈ L := by
    rw [hw]
    exact L.mul_mem ((mem_set_normalizer_iff.mp hgN _).mp huL) (L.inv_mem huL)
  have hwZ : (g * t * g⁻¹) * t⁻¹ ∈ zOf T :=
    (zOf T).mul_mem (h.F_zOf g hgF t ht) ((zOf T).inv_mem ht)
  have hw1 : (g * t * g⁻¹) * t⁻¹ ≠ 1 := fun e => hgt (mul_inv_eq_one.mp e)
  have hZle : ∀ s ∈ zOf T, s ∈ L := fun s hs => by
    obtain ⟨m, hm⟩ := h.exists_zpow_of_mem_zOf hwZ hw1 s hs
    rw [← hm]
    exact L.zpow_mem hwL m
  obtain ⟨s, hs, hs1⟩ := h.exists_ne_one_zOf
  apply hs1
  refine hinf s (hZle s hs) ((hmem' s).mpr (hZle _ ?_))
  have := h.F_zOf f⁻¹ (F.inv_mem hf) s hs
  simpa using this

end Case2Data

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
