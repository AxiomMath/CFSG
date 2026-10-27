module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSSpecial
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.I2Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.I2Rigid
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.I2Struct
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.Setting

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.Native

theorem HasModel.admZ {M : Type*} [Group M] {z : M} {E : Subgroup M} (hm : HasModel z E) :
    AdmZ z E := by
  obtain ⟨e, h, r, hE, hab, hcard, hz, htr, -⟩ := hm
  exact ⟨hab, hcard, hz, fun x hx hne => (htr x hx hne).imp fun a ha => ha.2⟩

theorem hasModel_of_admZ
    {M : Type*} [Group M] (σ : M ≃* ↥hs100P) {T : Subgroup M}
    {z : M} (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) (hz2 : orderOf z = 2)
    (hcent : centralizer (T : Set M) = zpowers z) {F : Subgroup M} (hF : AdmZ z F) :
    HasModel z F := by
  obtain ⟨T₀, hzP, hstd⟩ := zas_std_Q_explicit
  obtain ⟨σ', -, hz⟩ := exists_equiv_std hstd σ hT hTi hz2 hcent
  obtain ⟨hzP', E₀, hE₀⟩ := hs100_hasModel
  have e : σ'.symm ⟨zasZ0, hzP⟩ = z := by rw [← hz]; simp
  have hm : HasModel z (E₀.map σ'.symm.toMonoidHom) := by
    have := hE₀.map σ'.symm
    rwa [e] at this
  have hadm : AdmZ z (E₀.map σ'.symm.toMonoidHom) := by
    have := hE₀.admZ.map σ'.symm
    rwa [e] at this
  obtain ⟨c, hc, hcF⟩ := uniq_internal_of_std hstd σ' hT hTi hz2 hcent hF hadm
  have hcz : c * z = z * c := mem_centralizer_singleton_iff.1 hc
  have h1 := hm.map (MulAut.conj c).symm
  have h2 : (MulAut.conj c).symm z = z := by
    rw [MulAut.conj_symm_apply]
    calc c⁻¹ * z * c = c⁻¹ * (z * c) := by rw [mul_assoc]
      _ = c⁻¹ * (c * z) := by rw [hcz]
      _ = z := by group
  rw [h2, ← hcF] at h1
  have h3 : (F.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c).symm.toMonoidHom = F := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id F
    ext x
    simp
  rwa [h3] at h1

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] [Finite G] {W : Subgroup G} {g : G}
    (hg : ∀ w ∈ W, g * w * g⁻¹ ∈ W) : g ∈ normalizer (W : Set G) := by
  let f : W → W := fun w => ⟨g * w * g⁻¹, hg w w.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hsurj := Finite.surjective_of_injective hinj
  rw [mem_normalizer_iff]
  intro w
  refine ⟨fun hw => hg w hw, fun hw => ?_⟩
  obtain ⟨w', hw'⟩ := hsurj ⟨g * w * g⁻¹, hw⟩
  have h1 : g * (w' : G) * g⁻¹ = g * w * g⁻¹ := congrArg Subtype.val hw'
  have : (w' : G) = w := mul_left_cancel (mul_right_cancel h1)
  rw [← this]
  exact w'.2

theorem hsInner_I2
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsSporadic L .HS) {t : G} (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {S : Subgroup G} {z n : G}
    (hf : HSFusionData L t S z n) {E : Subgroup G} (hEL : E ≤ L) (hzE : z ∈ E)
    (hEab : IsElemAbelian 2 E) (hE16 : Nat.card E = 16)
    (hEconj : ∀ e ∈ E, e ≠ 1 → ∃ k ∈ L, k * z * k⁻¹ = e)
    (hfus : ∀ e ∈ E, ∃ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G),
      m * t * m⁻¹ = t * e) :
    ∃ W : Subgroup G, W ≤ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G) ∧
      (∀ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G), ∀ w ∈ W, m * w * m⁻¹ ∈ W) ∧
      E ≤ W ∧ t ∉ W ∧ IsElemAbelian 2 W ∧ Nat.card W = 256 ∧
      Nat.card (normalizer ((zpowers t ⊔ E : Subgroup G) : Set G)) = 16 * 23040 ∧
      centralizer ((zpowers t ⊔ E : Subgroup G) : Set G) = zpowers t ⊔ E ∧
      W = Opp2 (normalizer ((zpowers t ⊔ E : Subgroup G) : Set G)) := by
  classical
  obtain ⟨e₀⟩ := id hL
  let σ : ↥L ≃* ↥hs100P := (e₀ : ↥L ≃* NativeSporadic.HS).trans hs100Equiv
  have hSL := fusionData_relIndex_odd hf hL htL ht2 hin
  obtain ⟨hp, hi, ho, hc⟩ := internal_hyps hf.pgroup hSL ⟨hf.zS, hf.zL⟩ hf.z2 hf.zc
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    have := hEab.1
    rw [isMulCommutative_iff_of_setLike] at this
    exact this
  have hF : AdmZ (⟨z, hf.zL⟩ : ↥L) (E.subgroupOf L) := by
    refine ⟨⟨isMulCommutative_iff_of_setLike.2 fun a ha b hb => Subtype.ext (hcommE a ha b hb),
      fun x hx => Subtype.ext (by simpa using hEab.2 x hx)⟩, ?_, mem_subgroupOf.2 hzE, ?_⟩
    · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv).trans hE16
    · intro x hx hne
      obtain ⟨k, hk, hkx⟩ := hEconj (x : G) hx (fun h1 => hne (Subtype.ext h1))
      exact ⟨⟨k, hk⟩, Subtype.ext hkx⟩
  obtain ⟨e', h', r', hE, -, -, -, htr, hH, hN, hC, hh, hr0, hr1, hrH, hr2, hr01⟩ :=
    hasModel_of_admZ σ hp hi ho hc hF
  let e : Fin 4 → G := fun i => (e' i : G)
  let h : Fin 2 → G := fun j => (h' j : G)
  let r : Fin 2 → G := fun j => (r' j : G)
  have hmapc : ∀ {m : ℕ} (c : Fin m → ↥L),
      (Subgroup.closure (Set.range c)).map L.subtype =
        Subgroup.closure (Set.range fun i => (c i : G)) := by
    intro m c
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hEeq : E = Subgroup.closure (Set.range e) := by
    rw [← hmapc, ← hE, Subgroup.map_subgroupOf_eq_of_le hEL]
  have hNL : normalizer (E : Set G) ⊓ L = Subgroup.closure (Set.range h) := by
    rw [← hmapc, hH, ← Subgroup.subgroupOf_normalizer_eq hEL, Subgroup.subgroupOf_map_subtype]
  have hcard : Nat.card (normalizer (E : Set G) ⊓ L : Subgroup G) = 11520 := by
    rw [← hN, ← Subgroup.subgroupOf_normalizer_eq hEL, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : normalizer (E : Set G) ⊓ L ≤ L)).toEquiv]
  have hs : Setting L E t z :=
    { htL := htL
      ht2 := ht2
      hin := hin
      hLC := inf_centralizer_eq_bot_hs hL
      hEL := hEL
      hEab := hEab
      hE16 := hE16
      hzE := hzE
      hCE := by
        ext x
        constructor
        · rintro ⟨hxC, hxL⟩
          have hx : (⟨x, hxL⟩ : ↥L) ∈ centralizer ((E.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
            rw [mem_centralizer_iff]
            intro g hg
            exact Subtype.ext (mem_centralizer_iff.1 hxC (g : G) hg)
          rw [hC] at hx
          exact hx
        · intro hx
          exact ⟨mem_centralizer_iff.2 fun g hg => hcommE g hg x hx, hEL hx⟩
      hNE := hcard
      htrans := by
        intro x hx hne
        obtain ⟨a, ha, hax⟩ := htr ⟨x, hEL hx⟩ hx (fun h1 => hne (congrArg Subtype.val h1))
        rw [← Subgroup.subgroupOf_normalizer_eq hEL] at ha
        exact ⟨(a : G), ⟨ha, a.2⟩, congrArg Subtype.val hax⟩
      hzt := fusionData_conj_ne_z hf hL htL ht2 hin
      hfus := hfus }
  have heh : ∀ j, h j ∈ normalizer (E : Set G) ⊓ L := fun j => by
    rw [hNL]; exact Subgroup.subset_closure ⟨j, rfl⟩
  have hrN : ∀ j, r j ∈ Subgroup.closure (Set.range h) := fun j => by
    have := Subgroup.mem_map_of_mem L.subtype (hrH j)
    rwa [hmapc] at this
  obtain ⟨W, hEW, hWK, htW, hWab, hW256, hWh, hWKn⟩ := exists_elemAbelian_complement
    (E := E) (K := Ks t E) (t := t) e h r rho kx ky quadRigid_rho splitRigid_rho commRigid_rho
    z4Rigid_kx_ky hEeq hEab hE16 hs.tt hs.t_not_mem_E (fun a ha => hs.t_comm_E ha)
    (fun a ha => hs.X_le_K (mem_sup_right ha)) (hs.X_le_K (Setting.t_mem_X t E))
    (fun a ha b hb => (mem_centralizer_iff.1 hb.2 a ha))
    (fun k hk hkt => by
      rw [← hs.K_inf_t]
      exact ⟨hk, mem_centralizer_singleton_iff.2 hkt⟩)
    (fun k hk => hs.phi_mem hk) hs.phi_surj
    (fun j => hs.t_comm (h' j).2)
    (fun j k hk => hs.conj_mem_K (hs.A_le_N0 (heh j)).1 hk)
    (fun j i => by
      have := congrArg L.subtype (hh j i)
      rw [map_mul, map_mul, map_inv, map_vecE] at this
      exact this)
    (fun j => mem_sup_left (hrN j))
    (fun i => ⟨by
      have := congrArg L.subtype (hr0 i)
      rw [map_mul, map_mul, map_inv, map_vecE] at this
      exact this, by
      have := congrArg L.subtype (hr1 i)
      rw [map_mul, map_mul, map_inv, map_vecE] at this
      exact this⟩)
    (fun j => hr2 j) hr01
  have hWNK : ∀ g ∈ Ks t E, g ∈ normalizer (W : Set G) := fun g hg =>
    mem_normalizer_of_conj_mem (hWKn g hg)
  have hWNh : ∀ j, h j ∈ normalizer (W : Set G) := fun j =>
    mem_normalizer_of_conj_mem (hWh j)
  have hNLW : (normalizer (E : Set G) ⊓ L : Subgroup G) ≤ normalizer (W : Set G) := by
    rw [hNL, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact hWNh j
  have hN0W : N0s t E ≤ normalizer (W : Set G) := by
    rw [hs.N0_eq]
    refine sup_le hNLW ?_
    rw [zpowers_le]
    exact hWNK t (hs.X_le_K (Setting.t_mem_X t E))
  have hWN : ∀ m ∈ Ns t E, ∀ w ∈ W, m * w * m⁻¹ ∈ W := by
    intro m hm w hw
    obtain ⟨k, hk, n₀, hn₀, rfl⟩ := hs.N_eq m hm
    have hmn : k * n₀ ∈ normalizer (W : Set G) := mul_mem (hWNK k hk) (hN0W hn₀)
    exact (mem_normalizer_iff.1 hmn w).1 hw
  refine ⟨W, fun x hx => (hWK hx).1, hWN, hEW, htW, hWab, hW256, ?_, hs.centralizer_X, ?_⟩
  · rw [hs.card_N, hs.card_N0]
  · exact hs.O2O2_eq hWK hWN hEW htW hWab hW256

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2
