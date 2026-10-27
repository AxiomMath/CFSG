module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieces
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieceTorusCentral
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieceTorusElement
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieceTorusLift

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

namespace SPLMSide

variable {G : Type} [Group G] {p : ℕ} {M : Subgroup G} {z : G}

theorem eq_of_mk_eq_of_mem_centralizer {hzM : z ∈ M} (hcent : SPLCentralizerFacts p M hzM)
    {a b : M} (ha : (a : G) ∈ Subgroup.centralizer ({z} : Set G))
    (hb : (b : G) ∈ Subgroup.centralizer ({z} : Set G))
    (h : QuotientGroup.mk' (CFSG.pCore 2 ↥M) a = QuotientGroup.mk' (CFSG.pCore 2 ↥M) b) :
    a = b := by
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (a⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 : ((a⁻¹ * b : M) : G) ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) :=
    ⟨coe_mem_pCoreOf_two_of_mk_eq_one _ h1, by
      simpa using (Subgroup.centralizer ({z} : Set G)).mul_mem
        ((Subgroup.centralizer ({z} : Set G)).inv_mem ha) hb⟩
  rw [hcent.twoCore_inf, Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.mp (Subtype.ext h2)

theorem card_barM_of_le_centralizer {hzM : z ∈ M} (hcent : SPLCentralizerFacts p M hzM)
    {S : Subgroup G} (hSC : S ≤ Subgroup.centralizer ({z} : Set G)) (hSM : S ≤ M) :
    Nat.card (barM M S) = Nat.card S := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv]
  refine (Nat.card_congr (Equiv.ofBijective _ ⟨fun a b hab => ?_,
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).subgroupMap_surjective (S.subgroupOf M)⟩)).symm
  exact Subtype.ext (eq_of_mk_eq_of_mem_centralizer hcent (hSC (Subgroup.mem_subgroupOf.mp a.2))
    (hSC (Subgroup.mem_subgroupOf.mp b.2)) (congrArg Subtype.val hab))

theorem relIndex_barM_of_card {hzM : z ∈ M} (hcent : SPLCentralizerFacts p M hzM) (hp : p.Prime)
    {X T : Subgroup G} (hTC : T ≤ Subgroup.centralizer ({z} : Set G)) (hTM : T ≤ M)
    (hXT : X ≤ T) (hcard : Nat.card T = p ^ 6) (hX : Nat.card (barM M X) = p ^ 2) :
    (barM M X).relIndex (barM M T) = p ^ 4 := by
  have hle : barM M X ≤ barM M T := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hXT (Subgroup.mem_subgroupOf.mp hx))
  have h := Subgroup.relIndex_mul_relIndex ⊥ (barM M X) (barM M T) bot_le hle
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, hX,
    card_barM_of_le_centralizer hcent hTC hTM, hcard, show p ^ 6 = p ^ 2 * p ^ 4 by ring] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h

theorem conj_mem_barM_of_lift {hzM : z ∈ M} (hcent : SPLCentralizerFacts p M hzM)
    {T : Subgroup G} (hTM : T ≤ M)
    (hnorm : ∀ g ∈ Subgroup.centralizer ({z} : Set G) ⊓ M, ∀ t ∈ T, ∃ t' ∈ T,
      ∃ o ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)), g * t * g⁻¹ = t' * o) :
    ∀ g ∈ Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
    ∀ t ∈ barM M T, ∃ t' ∈ barM M T,
      ∃ o ∈ barM M (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))),
        g * t * g⁻¹ = t' * o := by
  rintro g hg _ ⟨t, ht, rfl⟩
  obtain ⟨m, hmC, rfl⟩ := hcent.lift g hg
  obtain ⟨t', ht', o, ho, heq⟩ := hnorm m ⟨hmC, m.2⟩ t (Subgroup.mem_subgroupOf.mp ht)
  refine ⟨_, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (show
    ((⟨t', hTM ht'⟩ : M) : G) ∈ T from ht')), _, Subgroup.mem_map_of_mem _
    (Subgroup.mem_subgroupOf.mpr (show ((⟨o, hcent.core_le ho⟩ : M) : G) ∈ _ from ho)), ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext (by simpa using heq))

theorem eq_or_eq_barM_of_lift {X T : Subgroup G} {c₀ : G} (hc₀ : c₀ ∈ M) (hTM : T ≤ M)
    (hXT : X ≤ T) (hcT : ∀ t ∈ T, c₀ * t * c₀⁻¹ ∈ T)
    (hirr : ∀ W : Subgroup G, X ≤ W → W ≤ T → (∀ w ∈ W, c₀ * w * c₀⁻¹ ∈ W) →
      W = X ∨ W = T) :
    ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), barM M X ≤ V → V ≤ barM M T →
      (∀ v ∈ V, splBar hc₀ * v * (splBar hc₀)⁻¹ ∈ V) → V = barM M X ∨ V = barM M T := by
  intro V hXV hVT hcV
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set W : Subgroup G := T ⊓ (V.comap mk).map M.subtype
  have hmemW : ∀ t (ht : t ∈ T), mk ⟨t, hTM ht⟩ ∈ V → t ∈ W :=
    fun t ht hv => ⟨ht, ⟨t, hTM ht⟩, hv, rfl⟩
  have hWmem : ∀ w ∈ W, ∃ hwM : w ∈ M, mk ⟨w, hwM⟩ ∈ V := by
    rintro w ⟨-, m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  have hXW : X ≤ W := fun x hx => hmemW x (hXT hx)
    (hXV (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)))
  have hcW : ∀ w ∈ W, c₀ * w * c₀⁻¹ ∈ W := by
    intro w hw
    obtain ⟨hwM, hwV⟩ := hWmem w hw
    refine hmemW _ (hcT w hw.1) ?_
    have h := hcV _ hwV
    have heq : mk ⟨c₀ * w * c₀⁻¹, hTM (hcT w hw.1)⟩ =
        splBar hc₀ * mk ⟨w, hwM⟩ * (splBar hc₀)⁻¹ := by
      rw [splBar, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rwa [heq]
  rcases hirr W hXW inf_le_left hcW with h | h
  · refine Or.inl (le_antisymm (fun v hv => ?_) hXV)
    obtain ⟨t, ht, rfl⟩ := hVT hv
    have htW : (t : G) ∈ W := hmemW _ (Subgroup.mem_subgroupOf.mp ht) hv
    rw [h] at htW
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htW)
  · refine Or.inr (le_antisymm hVT ?_)
    rintro _ ⟨t, ht, rfl⟩
    have htW : (t : G) ∈ W := by
      rw [h]
      exact Subgroup.mem_subgroupOf.mp ht
    exact (hWmem _ htW).2

theorem eq_one_barM_of_lift {hzM : z ∈ M} (hcent : SPLCentralizerFacts p M hzM) {T : Subgroup G}
    (hTC : T ≤ Subgroup.centralizer ({z} : Set G)) (hTM : T ≤ M)
    (hodd : ∀ j ∈ Subgroup.centralizer ({z} : Set G) ⊓ M, (∀ t ∈ T, j * t = t * j) →
      j ^ 2 = 1 → j = 1) :
    ∀ j ∈ Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      (∀ t ∈ barM M T, j * t = t * j) → j ^ 2 = 1 → j = 1 := by
  intro j hj hjT hj2
  set C := Subgroup.centralizer ({z} : Set G)
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  obtain ⟨m, hmC, rfl⟩ := hcent.lift j hj
  have hcomm : ∀ t ∈ T, (m : G) * t = t * m := by
    intro t ht
    have h := hjT (mk ⟨t, hTM ht⟩)
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (show
        ((⟨t, hTM ht⟩ : M) : G) ∈ T from ht)))
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (eq_of_mk_eq_of_mem_centralizer hcent
      (C.mul_mem hmC (hTC ht)) (C.mul_mem (hTC ht) hmC) h)
  have hm2 : (m : G) ^ 2 = 1 := by
    rw [← map_pow] at hj2
    have h := eq_of_mk_eq_of_mem_centralizer hcent (a := m ^ 2) (b := 1)
      (by simpa using C.pow_mem hmC 2) (by simp) (by rw [hj2, map_one])
    simpa using congrArg Subtype.val h
  rw [show m = 1 from Subtype.ext (hodd m ⟨hmC, m.2⟩ hcomm hm2), map_one]

theorem splTorusFacts_of_lift {hzM : z ∈ M} {X T : Subgroup G} (hcent : SPLCentralizerFacts p M hzM)
    (hblk : SPLBlockFacts p M X) {c₀ : G} (hc₀ : c₀ ∈ M) {r : ℕ}
    (hp : p.Prime) (hTC : T ≤ Subgroup.centralizer ({z} : Set G)) (hTM : T ≤ M)
    (hXT : X ≤ T) (hTp : IsPGroup p T) (hcard : Nat.card T = p ^ 6)
    (hTX : ∀ t ∈ T, ∀ x ∈ X, t * x = x * t)
    (hTO : ∀ t ∈ T, ∀ o ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)), t * o = o * t)
    (hTT : ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ X) (hTpow : ∀ a ∈ T, a ^ p = 1)
    (hnonab : ∃ a ∈ T, ∃ b ∈ T, a * b ≠ b * a)
    (hnorm : ∀ g ∈ Subgroup.centralizer ({z} : Set G) ⊓ M, ∀ t ∈ T, ∃ t' ∈ T,
      ∃ o ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)), g * t * g⁻¹ = t' * o)
    (hcC : c₀ ∈ Subgroup.centralizer ({z} : Set G)) (hcT : ∀ t ∈ T, c₀ * t * c₀⁻¹ ∈ T)
    (hcX : ∀ x ∈ X, c₀ * x = x * c₀) (hr : r.Prime) (hr1 : r ∣ p ^ 2 + 1)
    (hr2 : ¬ r ∣ p ^ 2 - 1)
    (hirr : ∀ W : Subgroup G, X ≤ W → W ≤ T → (∀ w ∈ W, c₀ * w * c₀⁻¹ ∈ W) →
      W = X ∨ W = T)
    (hodd : ∀ j ∈ Subgroup.centralizer ({z} : Set G) ⊓ M, (∀ t ∈ T, j * t = t * j) →
      j ^ 2 = 1 → j = 1) :
    SPLTorusFacts p M hzM X T hc₀ r := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hbar : ∀ {S : Subgroup G} {s : G} (hs : s ∈ S) (hsM : s ∈ M), mk ⟨s, hsM⟩ ∈ barM M S :=
    fun hs hsM => Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs)
  have hcomm : ∀ {a b : G} (haM : a ∈ M) (hbM : b ∈ M), a * b = b * a →
      mk ⟨a, haM⟩ * mk ⟨b, hbM⟩ = mk ⟨b, hbM⟩ * mk ⟨a, haM⟩ := by
    intro a b haM hbM hab
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hab)
  have hzc : ∀ {a : G} (haM : a ∈ M), a ∈ Subgroup.centralizer ({z} : Set G) →
      mk ⟨a, haM⟩ ∈ Subgroup.centralizer ({splBar hzM} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun haM ha => Subgroup.mem_centralizer_singleton_iff.mpr
      (hcomm haM hzM (Subgroup.mem_centralizer_singleton_iff.mp ha))
  exact
    { T_le := by
        rintro _ ⟨t, ht, rfl⟩
        exact hzc t.2 (hTC (Subgroup.mem_subgroupOf.mp ht))
      X_le := Subgroup.map_mono fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hXT (Subgroup.mem_subgroupOf.mp hx))
      T_p := (hTp.comap_subtype (K := M)).map _
      TO_norm := conj_mem_barM_of_lift hcent hTM hnorm
      T_X := by
        rintro _ ⟨t, ht, rfl⟩ _ ⟨x, hx, rfl⟩
        exact hcomm t.2 x.2 (hTX _ (Subgroup.mem_subgroupOf.mp ht) _
          (Subgroup.mem_subgroupOf.mp hx))
      T_O := by
        rintro _ ⟨t, ht, rfl⟩ _ ⟨o, ho, rfl⟩
        exact hcomm t.2 o.2 (hTO _ (Subgroup.mem_subgroupOf.mp ht) _
          (Subgroup.mem_subgroupOf.mp ho))
      TT := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        have h := hbar (hTT _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb))
          (M.mul_mem (M.mul_mem (M.mul_mem a.2 b.2) (M.inv_mem a.2)) (M.inv_mem b.2))
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        exact h
      Tp := by
        rintro _ ⟨a, ha, rfl⟩
        have h1 : a ^ p = 1 := Subtype.ext (by
          simpa using hTpow _ (Subgroup.mem_subgroupOf.mp ha))
        rw [← map_pow, h1, map_one]
        exact Subgroup.one_mem _
      index := relIndex_barM_of_card hcent hp hTC hTM hXT hcard hblk.X_card
      nonab := by
        obtain ⟨a, ha, b, hb, hab⟩ := hnonab
        refine ⟨_, hbar ha (hTM ha), _, hbar hb (hTM hb), fun h => hab ?_⟩
        rw [← map_mul, ← map_mul] at h
        exact congrArg Subtype.val (eq_of_mk_eq_of_mem_centralizer hcent
          (Subgroup.mul_mem _ (hTC ha) (hTC hb)) (Subgroup.mul_mem _ (hTC hb) (hTC ha)) h)
      c_mem := hzc hc₀ hcC
      c_T := by
        rintro _ ⟨t, ht, rfl⟩
        have h := hbar (hcT _ (Subgroup.mem_subgroupOf.mp ht))
          (M.mul_mem (M.mul_mem hc₀ t.2) (M.inv_mem hc₀))
        rw [splBar, ← map_inv, ← map_mul, ← map_mul]
        exact h
      c_X := by
        rintro _ ⟨x, hx, rfl⟩
        exact hcomm hc₀ x.2 (hcX _ (Subgroup.mem_subgroupOf.mp hx))
      r_prime := hr
      r_dvd := hr1
      r_ndvd := hr2
      irr := fun V hXV hVT _ hcV => eq_or_eq_barM_of_lift hc₀ hTM hXT hcT hirr V hXV hVT hcV
      CT_odd := eq_one_barM_of_lift hcent hTC hTM hodd }

end SPLMSide

theorem d1SPLPieceTorus_holds : D1SPLPieceTorus := by
  intro G _ _ p P M H R Rbar K z D hzM P' Pbar KC hRC hRP' hP'M htil hcent hblk
  have hp : p.Prime := D.data.cfg.red.prime
  have hp2 : p ≠ 2 := D.data.cfg.red.ne_two
  obtain ⟨hcard6, hpair⟩ := D.pair P' Pbar KC hRC hRP' hP'M
  have hXR : d1LiftX p H R K ≤ R := d1LiftX_le p H R K
  have hXC : d1LiftX p H R K ≤ Subgroup.centralizer ({z} : Set G) :=
    hXR.trans (D.data.le_centralizer_czElt D.czElt)
  have hTC := d1LiftX_le_H p (Subgroup.centralizer ({z} : Set G)) (P' : Subgroup G) KC
  have hTP := d1LiftX_le p (Subgroup.centralizer ({z} : Set G)) (P' : Subgroup G) KC
  have hTM := hTP.trans hP'M
  have hTp := P'.isPGroup'.to_le hTP
  have hTmap := SPLMSide.map_torusLift hRC
  have hXT := SPLMSide.le_torusLift (hXR.trans hRP') hXC hpair
  obtain ⟨r, hr, hr1, hr2, c, hc, hcr, hcT, hcZ, hcirr⟩ := htil.ppd
  obtain ⟨c₀, hc₀C, hc₀M, hπc, hc₀T, k, hk⟩ :=
    SPLMSide.exists_rElement_torusLift hp hTp hTC hTmap hcent.core_le hc hcT hr hcr
  subst hπc
  refine ⟨_, c₀, hc₀M, r, SPLMSide.splTorusFacts_of_lift hcent hblk hc₀M hp hTC hTM hXT hTp
    ((SPLMSide.card_torusLift hp hTp hTC hTmap).trans hcard6)
    (SPLMSide.commute_torusLift_of_mem hp hTp hTC hXT hTmap hpair)
    (SPLMSide.commute_glbPrimeCore_of_torusLift hRC.normal hTp hTC hXT hTmap hpair
      (fun x hx => SPLMSide.commute_glbPrimeCore_of_mem hzM hXC (hXT.trans hTM) hcent hblk x hx)
      htil)
    (SPLMSide.commutator_mem_of_torusLift hp hTp hTC hXT hTmap hpair htil)
    (SPLMSide.pow_eq_one_of_torusLift hp hTp hTC hTmap htil)
    (SPLMSide.exists_ne_of_torusLift hTmap htil)
    (SPLMSide.conj_mem_torusLift_mul hTC hTmap htil) hc₀C hc₀T
    (SPLMSide.commute_of_rElement hp hTp hTC hXT hpair hc₀C hc₀T hcZ) hr hr1 hr2
    (SPLMSide.eq_or_eq_of_rElement hp hTp hTC hXT hTmap hpair hc₀C hcirr)
    (SPLMSide.eq_one_of_commute_torusLift hp hp2 hTmap hcent.core_odd htil), k, ?_⟩
  have h1 : (⟨c₀, hc₀M⟩ : M) ^ r ^ k = 1 := Subtype.ext (by simpa using hk)
  rw [splBar, ← map_pow, h1, map_one]

end CFSG.AGLEmbedding
