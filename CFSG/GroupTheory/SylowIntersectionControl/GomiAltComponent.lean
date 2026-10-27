module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714AltAut
public import CFSG.GroupTheory.SylowIntersectionControl.GomiAltCore
import CFSG.GroupTheory.SylowIntersectionControl.AltNotIsolated
import CFSG.GroupTheory.SylowIntersectionControl.GomiComponentClauses
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact23Sylow
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedTransfer

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.GLS.IVK.Proofs2

section Map

variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G'] {p : ℕ} [Fact p.Prime]

theorem isPIsolatedOver_map_iff_of_ker_le {f : G →* G'} (hker : IsPGroup p f.ker)
    {H K : Subgroup G} (hkH : f.ker ≤ H) (hkK : f.ker ≤ K) :
    IsPIsolatedOver p (K.map f) (H.map f) ↔ IsPIsolatedOver p K H := by
  have hmap (Y : Subgroup G) : (Y.map f).subgroupOf f.range = Y.map f.rangeRestrict := by
    ext x
    simp [mem_subgroupOf, Subtype.ext_iff]
  rw [← isPIsolatedOver_subgroupOf_iff (map_le_range f H) (map_le_range f K), hmap, hmap]
  have hk : f.rangeRestrict.ker = f.ker := MonoidHom.ker_rangeRestrict f
  exact isPIsolatedOver_map_iff f.rangeRestrict_surjective (hk ▸ hker) (hk ▸ hkH) (hk ▸ hkK)

omit [Finite G] [Finite G'] in
theorem map_normalizer_eq_of_ker_le {f : G →* G'} {I : Subgroup G} (hk : f.ker ≤ I) :
    (normalizer (I : Set G)).map f =
      normalizer ((I.map f : Subgroup G') : Set G') ⊓ f.range := by
  have h := comap_normalizer_eq_of_le_range (map_le_range f I)
  rw [comap_map_eq_self hk] at h
  rw [← h, map_comap_eq, inf_comm]

theorem isPIsolatedOver_normalizer_map_iff {f : G →* G'} {I : Subgroup G} (hI : IsPGroup p I)
    (hk : f.ker ≤ I) :
    IsPIsolatedOver p (normalizer ((I.map f : Subgroup G') : Set G') ⊓ f.range) (I.map f) ↔
      IsPIsolatedOver p (normalizer (I : Set G)) I := by
  rw [← map_normalizer_eq_of_ker_le hk]
  exact isPIsolatedOver_map_iff_of_ker_le (hI.to_le hk) hk (hk.trans le_normalizer)

end Map

section Alt

variable {G : Type} [Group G] {n : ℕ} {A : Subgroup G}

@[expose] noncomputable def altNormalizerHom (hn : 7 ≤ n) (e : A ≃* alternatingGroup (Fin n)) :
    normalizer (A : Set G) →* Equiv.Perm (Fin n) :=
  (altAutEquiv hn e).toMonoidHom.comp A.normalizerMonoidHom

theorem altNormalizerHom_conj (hn : 7 ≤ n) (e : A ≃* alternatingGroup (Fin n))
    (u : normalizer (A : Set G)) {a : G} (ha : a ∈ A) :
    ((e ⟨(u : G) * a * (u : G)⁻¹, (u.2 a).mp ha⟩ : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)) =
      altNormalizerHom hn e u * e ⟨a, ha⟩ * (altNormalizerHom hn e u)⁻¹ :=
  altAutEquiv_spec hn e (A.normalizerMonoidHom u) ⟨a, ha⟩

theorem altNormalizerHom_of_mem (hn : 7 ≤ n) (e : A ≃* alternatingGroup (Fin n)) {a : G}
    (ha : a ∈ A) :
    altNormalizerHom hn e ⟨a, le_normalizer ha⟩ =
      ((e ⟨a, ha⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) :=
  (altAutEquiv_unique hn e _ (psiAlt e ⟨a, ha⟩) fun k => by
    have h : A.normalizerMonoidHom ⟨a, le_normalizer ha⟩ k = ⟨a, ha⟩ * k * (⟨a, ha⟩ : A)⁻¹ :=
      rfl
    rw [h, map_mul, map_mul, map_inv]).symm

theorem altNormalizerHom_eq_one_iff (hn : 7 ≤ n) (e : A ≃* alternatingGroup (Fin n))
    (u : normalizer (A : Set G)) :
    altNormalizerHom hn e u = 1 ↔ (u : G) ∈ centralizer (A : Set G) := by
  rw [← mem_subgroupOf, ← normalizerMonoidHom_ker, MonoidHom.mem_ker]
  exact (altAutEquiv hn e).map_eq_one_iff

theorem range_psiAlt (e : A ≃* alternatingGroup (Fin n)) :
    (psiAlt e).range = alternatingGroup (Fin n) := by
  ext σ
  refine ⟨fun ⟨a, ha⟩ => ha ▸ psiAlt_mem e a, fun hσ => ⟨e.symm ⟨σ, hσ⟩, ?_⟩⟩
  simp [psiAlt_apply]

private theorem normal_of_alternatingGroup_le (hn : 2 ≤ n) {X : Subgroup (Equiv.Perm (Fin n))}
    (hX : alternatingGroup (Fin n) ≤ X) : X.Normal := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have h := index_dvd_of_le hX
  rw [alternatingGroup.index_eq_two] at h
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
  · rw [index_eq_one.mp h]
    infer_instance
  · exact normal_of_index_eq_two h

private theorem ne_bot_of_isPIsolatedOver (hn : 7 ≤ n) {X H : Subgroup (Equiv.Perm (Fin n))}
    (hAX : alternatingGroup (Fin n) ≤ X)
    (h : IsPIsolatedOver 2 (normalizer (H : Set (Equiv.Perm (Fin n))) ⊓ X) H) : H ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro rfl
  have htop : normalizer ((⊥ : Subgroup (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n))) = ⊤ :=
    normalizer_eq_top _
  rw [htop, top_inf_eq] at h
  have h2 := h.of_isSubnormal_le_over IsPGroup.of_bot (le_top.trans htop.ge) bot_le le_rfl hAX
    (normal_subgroupOf (N := alternatingGroup (Fin n))).isSubnormal
    (by rw [relIndex_bot_left]; exact two_dvd_card_alternatingGroup (by omega))
  exact not_isPIsolatedOver_alternatingGroup hn
    (by simpa using (isPIsolatedOver_subgroupOf_iff bot_le le_rfl).mpr h2)

end Alt

section Q

variable {G : Type} [Group G] {n : ℕ} {A : Subgroup G}

private theorem mem_map_comap_psiAlt_iff (e : A ≃* alternatingGroup (Fin n))
    {Y : Subgroup (Equiv.Perm (Fin n))} {x : G} :
    x ∈ (Y.comap (psiAlt e)).map A.subtype ↔
      ∃ hx : x ∈ A, ((e ⟨x, hx⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ∈ Y := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

private theorem map_psiAlt_comap (e : A ≃* alternatingGroup (Fin n))
    (Y : Subgroup (Equiv.Perm (Fin n))) :
    (Y.comap (psiAlt e)).map (psiAlt e) = Y ⊓ alternatingGroup (Fin n) := by
  rw [map_comap_eq, range_psiAlt, inf_comm]

private theorem mem_normalizer_map_comap_psiAlt (hn : 7 ≤ n) (e : A ≃* alternatingGroup (Fin n))
    {Y : Subgroup (Equiv.Perm (Fin n))} {u : normalizer (A : Set G)}
    (hu : altNormalizerHom hn e u ∈ Y) :
    (u : G) ∈ normalizer (((Y.comap (psiAlt e)).map A.subtype : Subgroup G) : Set G) := by
  have key : ∀ v : normalizer (A : Set G), altNormalizerHom hn e v ∈ Y →
      ∀ x ∈ (Y.comap (psiAlt e)).map A.subtype,
        (v : G) * x * (v : G)⁻¹ ∈ (Y.comap (psiAlt e)).map A.subtype := by
    intro v hv x hx
    obtain ⟨hxA, hxY⟩ := (mem_map_comap_psiAlt_iff e).mp hx
    refine (mem_map_comap_psiAlt_iff e).mpr ⟨(v.2 x).mp hxA, ?_⟩
    rw [altNormalizerHom_conj hn e v hxA]
    exact mul_mem (mul_mem hv hxY) (inv_mem hv)
  refine B6.mem_normalizer_of_forall_mem (key u hu) fun x hx => ?_
  simpa using key u⁻¹ (by rw [map_inv]; exact inv_mem hu) x hx

private theorem inf_normalizer_map_comap_psiAlt_le (e : A ≃* alternatingGroup (Fin n))
    {Y : Subgroup (Equiv.Perm (Fin n))}
    (hNY : normalizer ((Y ⊓ alternatingGroup (Fin n) : Subgroup (Equiv.Perm (Fin n))) :
      Set (Equiv.Perm (Fin n))) = Y) :
    A ⊓ normalizer (((Y.comap (psiAlt e)).map A.subtype : Subgroup G) : Set G) ≤
      (Y.comap (psiAlt e)).map A.subtype := by
  rintro a ⟨haA, haN⟩
  have h : (⟨a, haA⟩ : A) ∈ normalizer ((Y.comap (psiAlt e) : Subgroup A) : Set A) := by
    have h1 := subgroupOf_normalizer_eq (map_subtype_le (Y.comap (psiAlt e)))
    rw [show ((Y.comap (psiAlt e)).map A.subtype).subgroupOf A = Y.comap (psiAlt e) from
      comap_map_eq_self_of_injective A.subtype_injective _] at h1
    rw [← h1]
    exact haN
  have h2 := le_normalizer_map (psiAlt e) (mem_map_of_mem (psiAlt e) h)
  rw [map_psiAlt_comap, hNY] at h2
  exact (mem_map_comap_psiAlt_iff e).mpr ⟨haA, h2⟩

private theorem map_comap_psiAlt_ne (e : A ≃* alternatingGroup (Fin n))
    {Y : Subgroup (Equiv.Perm (Fin n))} (hY : Y ≠ ⊤)
    (hNY : normalizer ((Y ⊓ alternatingGroup (Fin n) : Subgroup (Equiv.Perm (Fin n))) :
      Set (Equiv.Perm (Fin n))) = Y) :
    (Y.comap (psiAlt e)).map A.subtype ≠ A := by
  intro hQ
  have hAY : alternatingGroup (Fin n) ≤ Y := by
    rw [← range_psiAlt e]
    rintro _ ⟨a, rfl⟩
    obtain ⟨_, h⟩ := (mem_map_comap_psiAlt_iff e).mp (hQ.ge a.2)
    exact h
  exact hY (by rw [← hNY, inf_of_le_right hAY]; exact normalizer_eq_top _)

private theorem exists_isSylowTwoOf_le_normalizer_map_comap_psiAlt [Finite G] (hn : 7 ≤ n)
    (e : A ≃* alternatingGroup (Fin n)) {Y : Subgroup (Equiv.Perm (Fin n))} (hY : Odd Y.index) :
    ∃ T : Subgroup G, IsSylowTwoOf T (normalizer (A : Set G)) ∧
      T ≤ normalizer (((Y.comap (psiAlt e)).map A.subtype : Subgroup G) : Set G) := by
  have hR : alternatingGroup (Fin n) ≤ (altNormalizerHom hn e).range := by
    rw [← range_psiAlt e]
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨a, le_normalizer a.2⟩, altNormalizerHom_of_mem hn e a.2⟩
  have := normal_of_alternatingGroup_le (by omega) hR
  have hW : Odd (Y.comap (altNormalizerHom hn e)).index := by
    rw [index_comap, ← inf_relIndex_right, B6.relIndex_inf_eq_relIndex_sup
      (by rw [normalizer_eq_top _]; exact le_top)]
    exact hY.of_dvd_nat (relIndex_dvd_index_of_le le_sup_left)
  obtain ⟨T, hT, -⟩ := B6.exists_isSylowTwoOf_ge IsPGroup.of_bot
    (bot_le : ⊥ ≤ (Y.comap (altNormalizerHom hn e)).map (normalizer (A : Set G)).subtype)
  refine ⟨T, ⟨hT.1.trans (map_subtype_le _), hT.2.1, fun h => ?_⟩, fun t ht => ?_⟩
  · change 2 ∣ T.relIndex (normalizer (A : Set G)) at h
    rw [← relIndex_mul_relIndex _ _ _ hT.1 (map_subtype_le _)] at h
    change 2 ∣ _ * (((Y.comap (altNormalizerHom hn e)).map
      (normalizer (A : Set G)).subtype).subgroupOf (normalizer (A : Set G))).index at h
    rw [show ((Y.comap (altNormalizerHom hn e)).map (normalizer (A : Set G)).subtype).subgroupOf
      (normalizer (A : Set G)) = Y.comap (altNormalizerHom hn e) from
      comap_map_eq_self_of_injective (subtype_injective _) _] at h
    exact ((Nat.prime_two.dvd_mul).mp h).elim hT.2.2
      (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hW))
  · obtain ⟨u, hu, rfl⟩ := hT.1 ht
    exact mem_normalizer_map_comap_psiAlt hn e hu

private theorem charTwo_map_comap_psiAlt [Finite G] (e : A ≃* alternatingGroup (Fin n))
    {Y : Subgroup (Equiv.Perm (Fin n))} (h : CharTwo (Y ⊓ alternatingGroup (Fin n))) :
    CharTwo ((Y.comap (psiAlt e)).map A.subtype) := by
  rw [charTwo_iff_twoResidual_eq_bot, ← map_psiAlt_comap e,
    twoResidual_inf_centralizer_map (psiAlt_injective e),
    map_eq_bot_iff_of_injective _ (psiAlt_injective e)] at h
  rw [charTwo_iff_twoResidual_eq_bot, twoResidual_inf_centralizer_map A.subtype_injective, h,
    Subgroup.map_bot]

private theorem exists_twoResidual_le_zpowers [Finite G] (e : A ≃* alternatingGroup (Fin n))
    {Y : Subgroup (Equiv.Perm (Fin n))} {z : Equiv.Perm (Fin n)} (hz : z.IsThreeCycle)
    (h : twoResidual ((Y ⊓ alternatingGroup (Fin n)) ⊓ centralizer
      (pCoreOf 2 (Y ⊓ alternatingGroup (Fin n)) : Set (Equiv.Perm (Fin n)))) ≤ zpowers z) :
    ∃ x : G, ∃ hx : x ∈ A,
      ((e ⟨x, hx⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).IsThreeCycle ∧
        twoResidual ((Y.comap (psiAlt e)).map A.subtype ⊓
          centralizer (pCoreOf 2 ((Y.comap (psiAlt e)).map A.subtype) : Set G)) ≤ zpowers x := by
  set a : A := e.symm ⟨z, hz.mem_alternatingGroup⟩
  have ha : psiAlt e a = z := by simp [a, psiAlt_apply]
  refine ⟨a, a.2, by simpa [a] using hz, ?_⟩
  rw [← map_psiAlt_comap e, twoResidual_inf_centralizer_map (psiAlt_injective e), ← ha,
    ← MonoidHom.map_zpowers, map_le_map_iff_of_injective (psiAlt_injective e)] at h
  rw [twoResidual_inf_centralizer_map A.subtype_injective]
  exact (map_mono h).trans (MonoidHom.map_zpowers _ _).le

private theorem exists_of_gomiAltCore [Finite G] (hAlt : GomiAltCore) (hn : 7 ≤ n)
    (hn' : ∀ m : ℕ, n ≠ 2 ^ m + 1) (e : A ≃* alternatingGroup (Fin n)) {I : Subgroup G}
    (hIA : I ≤ normalizer (A : Set G)) (hI : IsPGroup 2 I)
    (hiso : IsPIsolatedOver 2 (normalizer (I : Set G) ⊓ (A ⊔ I)) I)
    (hC : (A ⊔ I) ⊓ centralizer (A : Set G) ≤ I) :
    ∃ Y : Subgroup (Equiv.Perm (Fin n)), Y ≠ ⊤ ∧ Odd Y.index ∧
      (∀ i (hi : i ∈ I), altNormalizerHom hn e ⟨i, hIA hi⟩ ∈ Y) ∧
      (∀ d ∈ A ⊓ normalizer (I : Set G), d ^ 2 ∈ I → ∀ hd, altNormalizerHom hn e ⟨d, hd⟩ ∈ Y) ∧
      normalizer ((Y ⊓ alternatingGroup (Fin n) : Subgroup (Equiv.Perm (Fin n))) :
        Set (Equiv.Perm (Fin n))) = Y ∧
      (Even n → CharTwo (Y ⊓ alternatingGroup (Fin n))) ∧
      (n % 4 = 3 → ∃ z : Equiv.Perm (Fin n), z.IsThreeCycle ∧
        twoResidual ((Y ⊓ alternatingGroup (Fin n)) ⊓ centralizer
          (pCoreOf 2 (Y ⊓ alternatingGroup (Fin n)) : Set (Equiv.Perm (Fin n)))) ≤ zpowers z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : A ⊔ I ≤ normalizer (A : Set G) := sup_le le_normalizer hIA
  obtain ⟨f, hf⟩ : ∃ f : (A ⊔ I : Subgroup G) →* Equiv.Perm (Fin n),
      ∀ u, f u = altNormalizerHom hn e (inclusion hU u) :=
    ⟨(altNormalizerHom hn e).comp (inclusion hU), fun _ => rfl⟩
  have hk : f.ker ≤ I.subgroupOf (A ⊔ I) := fun u hu =>
    hC ⟨u.2, (altNormalizerHom_eq_one_iff hn e _).mp ((hf u).symm.trans hu)⟩
  have hI' : IsPGroup 2 (I.subgroupOf (A ⊔ I)) := hI.comap_subtype
  have h1 := (isPIsolatedOver_subgroupOf_iff (le_sup_right : I ≤ A ⊔ I) inf_le_right).mpr hiso
  rw [inf_subgroupOf_right, subgroupOf_normalizer_eq le_sup_right] at h1
  have h2 := (isPIsolatedOver_normalizer_map_iff hI' hk).mpr h1
  have hAX : alternatingGroup (Fin n) ≤ f.range := by
    rw [← range_psiAlt e]
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨a, le_sup_left (a := A) a.2⟩, (hf _).trans (altNormalizerHom_of_mem hn e a.2)⟩
  obtain ⟨Y, hY, hYo, ⟨K, hHK, hKX, hKs, hK2, hKY⟩, hNY, hc, hz⟩ := hAlt n hn hn' f.range
    ((I.subgroupOf (A ⊔ I)).map f) hAX (ne_bot_of_isPIsolatedOver hn hAX h2) (hI'.map f)
    (map_le_range f _) h2
  refine ⟨Y, hY, hYo, fun i hi => ?_, fun d hd hd2 _ => ?_, hNY, hc, hz⟩
  · have h := hKY (hHK ⟨⟨i, le_sup_right (a := A) hi⟩, hi, rfl⟩)
    rwa [hf] at h
  have hdU : (⟨d, le_sup_left (a := A) hd.1⟩ : (A ⊔ I : Subgroup G)) ∈
      normalizer ((I.subgroupOf (A ⊔ I) : Subgroup _) : Set _) :=
    (subgroupOf_normalizer_eq le_sup_right).le hd.2
  have hd2': (⟨d, le_sup_left (a := A) hd.1⟩ : (A ⊔ I : Subgroup G)) ^ 2 ∈
      I.subgroupOf (A ⊔ I) := by
    rw [mem_subgroupOf, SubgroupClass.coe_pow]
    exact hd2
  have h := h2.mem_of_isSubnormal_over (hI'.map f) (le_inf le_normalizer (map_le_range f _))
    inf_le_left hHK hKX hKs hK2
    ⟨le_normalizer_map f (mem_map_of_mem f hdU), MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩
    ⟨_, hd2', map_pow f _ 2⟩
  rw [hf] at h
  exact hKY h

theorem exists_inf_of_gomiAltCore [Finite G] (hAlt : GomiAltCore) (hn : 7 ≤ n)
    (hn' : ∀ m : ℕ, n ≠ 2 ^ m + 1) (e : A ≃* alternatingGroup (Fin n)) {I : Subgroup G}
    (hIA : I ≤ normalizer (A : Set G)) (hI : IsPGroup 2 I)
    (hiso : IsPIsolatedOver 2 (normalizer (I : Set G) ⊓ (A ⊔ I)) I)
    (hC : (A ⊔ I) ⊓ centralizer (A : Set G) ≤ I) :
    ∃ Q : Subgroup G, Q ≤ A ∧ Q ≠ A ∧ A ⊓ normalizer (Q : Set G) ≤ Q ∧
      (∃ T : Subgroup G, IsSylowTwoOf T (normalizer (A : Set G)) ∧
        T ≤ normalizer (Q : Set G)) ∧ I ≤ normalizer (Q : Set G) ∧
      (∀ d ∈ A ⊓ normalizer (I : Set G), d ^ 2 ∈ I → d ∈ Q) ∧ (Even n → CharTwo Q) ∧
      (n % 4 = 3 → ∃ z : G, ∃ hz : z ∈ A,
        ((e ⟨z, hz⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).IsThreeCycle ∧
          twoResidual (Q ⊓ centralizer (pCoreOf 2 Q : Set G)) ≤ zpowers z) := by
  obtain ⟨Y, hY, hYo, hIY, hDY, hNY, hc, hz⟩ :=
    exists_of_gomiAltCore hAlt hn hn' e hIA hI hiso hC
  refine ⟨(Y.comap (psiAlt e)).map A.subtype, map_subtype_le _, map_comap_psiAlt_ne e hY hNY,
    inf_normalizer_map_comap_psiAlt_le e hNY,
    exists_isSylowTwoOf_le_normalizer_map_comap_psiAlt hn e hYo,
    fun i hi => mem_normalizer_map_comap_psiAlt hn e (hIY i hi),
    fun d hd hd2 => (mem_map_comap_psiAlt_iff e).mpr ⟨hd.1, ?_⟩,
    fun h => charTwo_map_comap_psiAlt e (hc h), fun h => ?_⟩
  · rw [← altNormalizerHom_of_mem hn e hd.1]
    exact hDY d hd hd2 _
  · obtain ⟨z, hz3, hzY⟩ := hz h
    exact exists_twoResidual_le_zpowers e hz3 hzY

end Q

end CFSG.GroupTheory

end
