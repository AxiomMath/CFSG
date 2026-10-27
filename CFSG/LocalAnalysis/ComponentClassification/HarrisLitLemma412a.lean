module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open Standing.Setup42
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem commutator_eq_self_or_eq_bot {G : Type*} [Group G] {H T : Subgroup G} [H.Normal]
    (hH : IsQuasisimple ↥H) : ⁅H, T⁆ = H ∨ ⁅H, T⁆ = ⊥ := by
  have hNH : ⁅H, T⁆ ≤ H := commutator_le_left H T
  have hnorm : (⁅H, T⁆.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNH).mpr (normalizer_commutator_ge_left H T)
  rcases LocalCores.quasisimple_normal_subgroups hH hnorm with htop | hcen
  · left
    refine le_antisymm hNH fun x hx => ?_
    have : (⟨x, hx⟩ : ↥H) ∈ ⁅H, T⁆.subgroupOf H := by rw [htop]; exact mem_top _
    exact this
  · right
    have hNC : ⁅H, T⁆ ≤ centralizer (H : Set G) := fun x hx =>
      mem_centralizer_iff.mpr fun y hy => by
        have := mem_center_iff.mp (hcen (show (⟨x, hNH hx⟩ : ↥H) ∈ ⁅H, T⁆.subgroupOf H from hx))
          ⟨y, hy⟩
        exact congrArg Subtype.val this
    have h1 : ⁅⁅H, T⁆, H⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hNC
    have h2 : ⁅⁅T, H⁆, H⁆ = ⊥ := by rw [commutator_comm T H]; exact h1
    have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
    have : Group.IsPerfect ↥H := hH.1
    rwa [commutator_eq_self] at h3

variable {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X} {i j : ℕ}

namespace Setting46e

theorem tBar_sq (hs : Setting46e t L p f S w z V i j) : hs.setup.tBar i j ^ 2 = 1 := by
  have ht2 : t ^ 2 = 1 := by
    rw [← hs.standing.config.orderOf_eq]
    exact pow_orderOf_eq_one t
  rw [tBar, ← QuotientGroup.mk_pow]
  rw [show (⟨t, hs.setup.t_mem_centralizer_beta i j⟩ :
      ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) ^ 2 = 1 from
    Subtype.ext (by rw [Subgroup.coe_pow, ht2, Subgroup.coe_one]), QuotientGroup.mk_one]

theorem betaBar_sq (hs : Setting46e t L p f S w z V i j) :
    betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ^ 2 = 1 := by
  rw [betaBar, ← QuotientGroup.mk_pow]
  rw [show (⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, mem_centralizer_singleton_iff.mpr rfl⟩ :
      ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) ^ 2 = 1 from
    Subtype.ext (by rw [Subgroup.coe_pow, hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j),
      Subgroup.coe_one]), QuotientGroup.mk_one]

theorem tBar_not_mem_pCore (hs : Setting46e t L p f S w z V i j) :
    hs.setup.tBar i j ∉ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set K := centralizerResidual L β with hK
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  intro htO
  obtain ⟨v, ⟨-, hvM⟩, -, -, hvt⟩ := hs.beta.exists_mem
  have hOK : pCore 2 (MBar β) ≤ centralizer (KBar L β : Set (MBar β)) :=
    le_sup_left.trans hs.lemma46f.1
  have htM : t ∈ M := hs.setup.t_mem_centralizer_beta i j
  have hβM : β ∈ M := mem_centralizer_singleton_iff.mpr rfl
  have hzK : z ∈ K := hs.lemma45.z_mem.2
  have hzM : z ∈ M := (centralizerResidual_le hzK).2
  have hτ : π ⟨v * t * v⁻¹, mul_mem (mul_mem hvM htM) (inv_mem hvM)⟩ ∈
      centralizer (KBar L β : Set (MBar β)) := by
    apply hOK
    have h1 := (pCore_normal (p := 2) (G := MBar β)).conj_mem _ htO (π ⟨v, hvM⟩)
    have h2 : π ⟨v * t * v⁻¹, mul_mem (mul_mem hvM htM) (inv_mem hvM)⟩ =
        π ⟨v, hvM⟩ * hs.setup.tBar i j * (π ⟨v, hvM⟩)⁻¹ := by
      rw [tBar, show (QuotientGroup.mk ⟨t, hs.setup.t_mem_centralizer_beta i j⟩ : MBar β) =
        π ⟨t, htM⟩ from rfl, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h2]
    exact h1
  have htC : π ⟨t, htM⟩ ∈ centralizer (KBar L β : Set (MBar β)) :=
    hs.setup.tBar_mem_centralizer_K i j
  have hbC : π ⟨β, hβM⟩ ∈ centralizer (KBar L β : Set (MBar β)) :=
    betaBar_mem_centralizer_K (L := L) β
  have hzC : π ⟨z, hzM⟩ ∈ centralizer (KBar L β : Set (MBar β)) := by
    rcases hvt with hvt | hvt
    · have h1 : (⟨z, hzM⟩ : ↥M) = ⟨t, htM⟩⁻¹ *
          ⟨v * t * v⁻¹, mul_mem (mul_mem hvM htM) (inv_mem hvM)⟩ :=
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; rw [hvt]; group)
      rw [h1, map_mul, map_inv]
      exact mul_mem (inv_mem htC) hτ
    · have h1 : (⟨z, hzM⟩ : ↥M) = (⟨t, htM⟩ * ⟨β, hβM⟩)⁻¹ *
          ⟨v * t * v⁻¹, mul_mem (mul_mem hvM htM) (inv_mem hvM)⟩ :=
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; rw [hvt, ← hβ]; group)
      rw [h1, map_mul, map_inv, map_mul]
      exact mul_mem (inv_mem (mul_mem htC hbC)) hτ
  have hKO : K ≤ (pPrimeCore 2 ↥M).map M.subtype := by
    have hcomm : ⁅K, zpowers z⁆ = K := by
      have := hs.lemma45.commutator_eq 1 (one_mem _)
      rwa [one_mul] at this
    refine hcomm ▸ commutator_le.mpr ?_
    intro k hk g hg
    have hkM : k ∈ M := (centralizerResidual_le hk).2
    have hgM : g ∈ M := (zpowers_le.mpr hzM) hg
    have hkK : π ⟨k, hkM⟩ ∈ KBar L β := ⟨⟨k, hkM⟩, hk, rfl⟩
    have hgC : π ⟨g, hgM⟩ ∈ centralizer (KBar L β : Set (MBar β)) := by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
      rw [show (⟨z ^ n, hgM⟩ : ↥M) = ⟨z, hzM⟩ ^ n from Subtype.ext (by simp), map_zpow]
      exact zpow_mem hzC n
    have hc := mem_centralizer_iff.mp hgC _ hkK
    refine ⟨⁅(⟨k, hkM⟩ : ↥M), ⟨g, hgM⟩⁆, ?_, rfl⟩
    show _ ∈ pPrimeCore 2 ↥M
    rw [← QuotientGroup.eq_one_iff]
    change π ⁅(⟨k, hkM⟩ : ↥M), ⟨g, hgM⟩⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hc]
  have hzO := hKO hzK
  have hdvd := Subgroup.orderOf_dvd_natCard _ hzO
  rw [hs.setup.z_order] at hdvd
  exact absurd hdvd (Nat.prime_two.coprime_iff_not_dvd.mp (coprime_card_map_pPrimeCore M))

theorem pCore_inf_centralizer_tBar (hs : Setting46e t L p f S w z V i j) :
    pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hs.setup.tBar i j} =
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  obtain ⟨-, -, hβmem, hle⟩ := hs.lemma46f
  apply le_antisymm
  · intro x hx
    have htb : hs.setup.tBar i j * betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
        betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * hs.setup.tBar i j :=
      mem_center_iff.mp (betaBar_mem_center _) _
    rcases mem_closure_pair hs.tBar_sq hs.betaBar_sq htb (hle hx) with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact absurd hx.1 hs.tBar_not_mem_pCore
    · exact mem_zpowers _
    · exfalso
      apply hs.tBar_not_mem_pCore
      have := (pCore 2 _).mul_mem hx.1 ((pCore 2 _).inv_mem hβmem.1)
      rwa [mul_inv_cancel_right] at this
  · exact zpowers_le.mpr hβmem

theorem KBar_le_layer (hs : Setting46e t L p f S w z V i j) :
    KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  rw [← hs.lemma46a.2]
  exact (map_subtype_le _).trans inf_le_left

theorem KBar_lt_layer (hs : Setting46e t L p f S w z V i j)
    (hg : IsLemma46g (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) <
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  refine lt_of_le_of_ne hs.KBar_le_layer fun heq => hs.tBar_not_mem_pCore ?_
  rw [hg.1, hg.2.1, ← heq]
  exact hs.setup.tBar_mem_centralizer_K i j

theorem layer_eq_commutator (hs : Setting46e t L p f S w z V i j)
    (hd : IsLemma46d p f L (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (hg : IsLemma46g (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      ⁅layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), zpowers (hs.setup.tBar i j)⁆ := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set tb := hs.setup.tBar i j with htb
  set E := layer (MBar β) with hE
  have : E.Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  have hNE : ⁅E, zpowers tb⁆ ≤ E := commutator_le_left E _
  rcases hd with ⟨hq, -⟩ | ⟨K₁, K₂, hsup, -, hcomm12, hmap, ⟨e₁⟩, -, hLie, -, -⟩
  · rcases commutator_eq_self_or_eq_bot (T := zpowers tb) hq with h | h
    · exact h.symm
    · exfalso
      apply hs.tBar_not_mem_pCore
      rw [hg.1, hg.2.1]
      have hle := commutator_eq_bot_iff_le_centralizer.mp h
      exact mem_centralizer_iff.mpr fun y hy =>
        (mem_centralizer_iff.mp (hle hy) tb (mem_zpowers _)).symm
  ·
    have hEN : E ≤ normalizer ((⁅E, zpowers tb⁆ : Subgroup (MBar β)) : Set (MBar β)) :=
      normalizer_commutator_ge_left E _
    have hTN : zpowers tb ≤ normalizer ((⁅E, zpowers tb⁆ : Subgroup (MBar β)) : Set (MBar β)) :=
      normalizer_commutator_ge_right E _
    have hK1E : K₁ ≤ E := le_sup_left.trans hsup.le
    have hK1 : ⁅K₁, K₁⁆ = K₁ := by
      have hsimp := isSimpleGroup_of_lieModel_psl2 hLie
      have hq := LocalCores.isQuasisimple_of_isSimpleGroup (nonabelian_of_lieModel_psl2 hLie)
      have : Group.IsPerfect ↥K₁ := (LocalCores.isQuasisimple_of_mulEquiv e₁.symm hq.1).1
      exact commutator_eq_self
    have hK1N : K₁ ≤ ⁅E, zpowers tb⁆ := by
      rw [← hK1, commutator_le]
      intro k hk k' hk'
      have ha : ⁅k, tb⁻¹⁆ ∈ ⁅E, zpowers tb⁆ :=
        commutator_mem_commutator (hK1E hk) (inv_mem (mem_zpowers _))
      have hb : ⁅⁅k, tb⁻¹⁆, k'⁆ ∈ ⁅E, zpowers tb⁆ := by
        have h1 : k' * ⁅k, tb⁻¹⁆⁻¹ * k'⁻¹ ∈ ⁅E, zpowers tb⁆ :=
          (mem_normalizer_iff.mp (hEN (hK1E hk')) _).mp (inv_mem ha)
        have h2 : ⁅⁅k, tb⁻¹⁆, k'⁆ = ⁅k, tb⁻¹⁆ * (k' * ⁅k, tb⁻¹⁆⁻¹ * k'⁻¹) := by
          rw [commutatorElement_def ⁅k, tb⁻¹⁆ k']
          group
        rw [h2]
        exact mul_mem ha h1
      have hc : tb⁻¹ * k⁻¹ * tb ∈ K₂ := by
        rw [← hmap]
        refine ⟨k⁻¹, inv_mem hk, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have hck : tb⁻¹ * k⁻¹ * tb * k' = k' * (tb⁻¹ * k⁻¹ * tb) :=
        (mem_centralizer_iff.mp (hcomm12 hk') _ hc)
      have h3 : ⁅⁅k, tb⁻¹⁆, k'⁆ = ⁅k, k'⁆ := by
        have h4 : ⁅k, tb⁻¹⁆ = k * (tb⁻¹ * k⁻¹ * tb) := by
          rw [commutatorElement_def, inv_inv]
          group
        rw [h4, commutatorElement_def, commutatorElement_def]
        calc k * (tb⁻¹ * k⁻¹ * tb) * k' * (k * (tb⁻¹ * k⁻¹ * tb))⁻¹ * k'⁻¹ =
              k * (tb⁻¹ * k⁻¹ * tb * k') * (tb⁻¹ * k⁻¹ * tb)⁻¹ * k⁻¹ * k'⁻¹ := by group
          _ = k * k' * k⁻¹ * k'⁻¹ := by rw [hck]; group
      rw [← h3]
      exact hb
    have hK2N : K₂ ≤ ⁅E, zpowers tb⁆ := by
      rw [← hmap]
      rintro _ ⟨k, hk, rfl⟩
      have := (mem_normalizer_iff.mp (hTN (inv_mem (mem_zpowers tb))) k).mp (hK1N hk)
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
    exact le_antisymm (hsup.symm.le.trans (sup_le hK1N hK2N)) hNE

end Setting46e

end CFSG.ComponentClassification.HarrisLit
