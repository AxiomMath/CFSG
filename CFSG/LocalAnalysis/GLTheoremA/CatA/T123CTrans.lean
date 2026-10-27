module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Compl123

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123C

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {A B : Type} [Group A] [Group B] [Finite A] [Finite B]

theorem map_glaPPrimeCore_equiv {A' : Type} [Group A'] (p : ℕ) (e : A ≃* A') :
    (GLAPPrimeCore p A).map (e : A →* A') = GLAPPrimeCore p A' := by
  unfold GLAPPrimeCore CFSG.pPrimeCore
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    apply sSup_le
    intro K hK
    obtain ⟨hKn, hKc⟩ := hK
    rw [← Subgroup.map_le_iff_le_comap]
    apply le_sSup
    refine ⟨hKn.map (e : A →* A') e.surjective, ?_⟩
    rw [Subgroup.card_map_of_injective e.injective]
    exact hKc
  · apply sSup_le
    intro K' hK'
    obtain ⟨hKn', hKc'⟩ := hK'
    have hcomap : (K'.comap (e : A →* A')).map (e : A →* A') = K' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective K'
    have hcard : Nat.card (K'.comap (e : A →* A')) = Nat.card K' := by
      rw [← Subgroup.card_map_of_injective (f := (e : A →* A')) e.injective (K := K'.comap (e : A →* A')),
        hcomap]
    have hmem : K'.comap (e : A →* A') ∈ {K : Subgroup A | K.Normal ∧ Nat.Coprime p (Nat.card K)} :=
      ⟨hKn'.comap (e : A →* A'), hcard ▸ hKc'⟩
    have hle := le_sSup hmem
    calc K' = (K'.comap (e : A →* A')).map (e : A →* A') := hcomap.symm
      _ ≤ _ := Subgroup.map_mono hle

theorem glaPPrimeCoreOf_map {f : A →* B} (hf : Function.Injective f) (p : ℕ) (M : Subgroup A) :
    GLAPPrimeCoreOf p (M.map f) = (GLAPPrimeCoreOf p M).map f := by
  unfold GLAPPrimeCoreOf
  have h1 := map_glaPPrimeCore_equiv (A := ↥M) (A' := ↥(M.map f)) p (Subgroup.equivMapOfInjective M f hf)
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem isElemAbelian_map_iff {f : A →* B} (hf : Function.Injective f) (p : ℕ) (E : Subgroup A) :
    CFSG.Open.IsElemAbelian p (E.map f) ↔ CFSG.Open.IsElemAbelian p E := by
  constructor
  · intro h
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hf
      have hc := h.1.is_comm.comm ⟨f a, ⟨a, a.2, rfl⟩⟩ ⟨f b, ⟨b, b.2, rfl⟩⟩
      have hc' := congrArg Subtype.val hc
      simpa using hc'
    · apply hf
      rw [map_pow, map_one]
      exact h.2 (f x) ⟨x, hx, rfl⟩
  · intro h
    exact h.map f

theorem centMod_map_iff {f : A →* B} (hf : Function.Injective f) (p : ℕ) (M : Subgroup A) (a : A) :
    CentMod p (M.map f) (f a) ↔ CentMod p M a := by
  unfold CentMod
  have hcomm : ⁅M.map f, Subgroup.zpowers (f a)⁆ = (⁅M, Subgroup.zpowers a⁆).map f := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
  constructor
  · rintro ⟨hn, hc⟩
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff] at hn ⊢
      intro m
      have key : ∀ n : A, f n ∈ M.map f ↔ n ∈ M := fun n => Subgroup.mem_map_iff_mem hf
      have := hn (f m)
      rw [← key m, ← key (a * m * a⁻¹)]
      simpa [map_mul, map_inv] using this
    · rw [hcomm, glaPPrimeCoreOf_map hf] at hc
      exact (Subgroup.map_le_map_iff_of_injective hf).1 hc
  · rintro ⟨hn, hc⟩
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hh
        have hm' : a * m * a⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.1 hn m).1 hm
        exact Subgroup.mem_map.2 ⟨a * m * a⁻¹, hm', by simp [map_mul, map_inv]⟩
      · intro hh
        obtain ⟨n, hn', hnf⟩ := Subgroup.mem_map.1 hh
        have hh2 : h = f (a⁻¹ * n * a) := by
          rw [map_mul, map_mul, map_inv, hnf]
          group
        have hmem : a⁻¹ * n * a ∈ M := by
          have e : a * (a⁻¹ * n * a) * a⁻¹ = n := by group
          exact (Subgroup.mem_normalizer_iff.1 hn (a⁻¹ * n * a)).2 (by rw [e]; exact hn')
        rw [hh2]
        exact Subgroup.mem_map.2 ⟨_, hmem, rfl⟩
    · rw [hcomm, glaPPrimeCoreOf_map hf]
      exact (Subgroup.map_le_map_iff_of_injective hf).2 hc

noncomputable def pSimpleEquiv (p : ℕ) {f : A →* B} (hf : Function.Injective f) (X : Subgroup A) :
    PSimple p X ≃* PSimple p (X.map f) := by
  have hPC : (GLAPPrimeCore p ↥X).map ((Subgroup.equivMapOfInjective X f hf : ↥X ≃* ↥(X.map f)) :
      ↥X →* ↥(X.map f)) = GLAPPrimeCore p ↥(X.map f) :=
    map_glaPPrimeCore_equiv p (Subgroup.equivMapOfInjective X f hf)
  let φ : PQuot p X ≃* PQuot p (X.map f) :=
    QuotientGroup.congr (GLAPPrimeCore p ↥X) (GLAPPrimeCore p ↥(X.map f)) (Subgroup.equivMapOfInjective X f hf) hPC
  exact QuotientGroup.congr (Subgroup.center (PQuot p X)) (Subgroup.center (PQuot p (X.map f))) φ
    (Subgroup.map_center_eq φ)

theorem catalogIs_pSimple_map_iff {f : A →* B} (hf : Function.Injective f) (p : ℕ) (X : Subgroup A)
    (Q : TauCeti.CFSGIndex → Prop) :
    catalogIs (PSimple p (X.map f)) Q ↔ catalogIs (PSimple p X) Q :=
  (catalogIs_congr (pSimpleEquiv p hf X)).symm

theorem isQuasisimple_map_iff {f : A →* B} (hf : Function.Injective f) (X : Subgroup A) :
    CFSG.Open.IsQuasisimple ↥(X.map f) ↔ CFSG.Open.IsQuasisimple ↥X := by
  constructor
  · intro h
    exact CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.equivMapOfInjective X f hf) h
  · intro h
    exact CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.equivMapOfInjective X f hf).symm h

theorem isSubnormal_map_iff {f : A →* B} (hf : Function.Injective f) {L X : Subgroup A} :
    CFSG.Open.IsSubnormal (L.map f) (X.map f) ↔ CFSG.Open.IsSubnormal L X := by
  constructor
  · intro h
    have h2 := CFSG.Open.IsSubnormal.comap f h
    rwa [Subgroup.comap_map_eq_self_of_injective hf, Subgroup.comap_map_eq_self_of_injective hf] at h2
  · intro h
    exact CFSG.Open.IsSubnormal.map f h

theorem subgroupOf_map_eq {f : A →* B} (hf : Function.Injective f) {X K : Subgroup A} (hK : K ≤ X) :
    (K.map f).subgroupOf (X.map f) =
      (K.subgroupOf X).map (Subgroup.equivMapOfInjective X f hf : ↥X →* ↥(X.map f)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨k, hk, hkf⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy)
    refine Subgroup.mem_map.2 ⟨⟨k, hK hk⟩, Subgroup.mem_subgroupOf.2 hk, ?_⟩
    exact Subtype.ext hkf
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, Subgroup.mem_subgroupOf.1 hx, rfl⟩)

theorem isComponentOf_top_map_iff {Q Q' : Type} [Group Q] [Group Q'] [Finite Q] [Finite Q'] (Φ : Q ≃* Q')
    (S : Subgroup Q) :
    CFSG.Open.IsComponentOf (S.map (Φ : Q →* Q')) ⊤ ↔ CFSG.Open.IsComponentOf S ⊤ := by
  have hsub : CFSG.Open.IsSubnormal (S.map (Φ : Q →* Q')) ⊤ ↔ CFSG.Open.IsSubnormal S ⊤ := by
    have h := isSubnormal_map_iff (f := (Φ : Q →* Q')) Φ.injective (L := S) (X := ⊤)
    rwa [Subgroup.map_top_of_surjective _ Φ.surjective] at h
  have hqs : CFSG.Open.IsQuasisimple ↥(S.map (Φ : Q →* Q')) ↔ CFSG.Open.IsQuasisimple ↥S :=
    isQuasisimple_map_iff Φ.injective S
  unfold CFSG.Open.IsComponentOf
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨le_top, hsub.1 h1, hqs.1 h2⟩
  · rintro ⟨-, h1, h2⟩
    exact ⟨le_top, hsub.2 h1, hqs.2 h2⟩

theorem glaPComponent_map_iff {f : A →* B} (hf : Function.Injective f) (p : ℕ) (X L : Subgroup A) :
    GLAPComponent p (X.map f) (L.map f) ↔ GLAPComponent p X L := by
  set ψ : ↥X ≃* ↥(X.map f) := Subgroup.equivMapOfInjective X f hf with hψ
  have hPC : (GLAPPrimeCore p ↥X).map (ψ : ↥X →* ↥(X.map f)) = GLAPPrimeCore p ↥(X.map f) :=
    map_glaPPrimeCore_equiv p ψ
  set Φ := QuotientGroup.congr (GLAPPrimeCore p ↥X) (GLAPPrimeCore p ↥(X.map f)) ψ hPC with hΦ
  have himg : ∀ K : Subgroup A, K ≤ X →
      ((K.map f).subgroupOf (X.map f)).map (QuotientGroup.mk' (GLAPPrimeCore p ↥(X.map f))) =
        ((K.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map (Φ : _ →* _) := by
    intro K hK
    rw [subgroupOf_map_eq hf hK, Subgroup.map_map, Subgroup.map_map]
    rfl
  unfold GLAPComponent
  constructor
  · rintro ⟨hLX, hsub, hic, hmin⟩
    have hLX' : L ≤ X := (Subgroup.map_le_map_iff_of_injective hf).1 hLX
    refine ⟨hLX', (isSubnormal_map_iff hf).1 hsub, ?_, ?_⟩
    · exact (isComponentOf_top_map_iff Φ _).1 (by rw [← himg L hLX']; exact hic)
    · intro J hJ hJs heq
      have hJL : J.map f < L.map f :=
        lt_of_le_of_ne (Subgroup.map_mono hJ.le) (fun h => hJ.ne (Subgroup.map_injective hf h))
      apply hmin (J.map f) hJL ((isSubnormal_map_iff hf).2 hJs)
      rw [himg J (hJ.le.trans hLX'), himg L hLX', heq]
  · rintro ⟨hLX', hsub, hic, hmin⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective hf).2 hLX', (isSubnormal_map_iff hf).2 hsub, ?_, ?_⟩
    · rw [himg L hLX']; exact (isComponentOf_top_map_iff Φ _).2 hic
    · intro J' hJ' hJ's heq
      have hLr : L.map f ≤ f.range := by
        rintro _ ⟨a, _, rfl⟩
        exact MonoidHom.mem_range.2 ⟨a, rfl⟩
      have hle : J' ≤ f.range := hJ'.le.trans hLr
      obtain ⟨J, rfl⟩ : ∃ J : Subgroup A, J.map f = J' := ⟨J'.comap f, Subgroup.map_comap_eq_self hle⟩
      have hJleL : J ≤ L := (Subgroup.map_le_map_iff_of_injective hf).1 hJ'.le
      have hJneL : J ≠ L := fun h => hJ'.ne (congrArg (Subgroup.map f) h)
      have hJlt : J < L := lt_of_le_of_ne hJleL hJneL
      have hJs : CFSG.Open.IsSubnormal J X := (isSubnormal_map_iff hf).1 hJ's
      have hJX : J ≤ X := hJlt.le.trans hLX'
      rw [himg J hJX, himg L hLX'] at heq
      have hinj : Function.Injective (Subgroup.map (Φ : (↥X ⧸ GLAPPrimeCore p ↥X) →*
          (↥(X.map f) ⧸ GLAPPrimeCore p ↥(X.map f)))) := Subgroup.map_injective Φ.injective
      exact hmin J hJlt hJs (hinj heq)
theorem type167_map_iff {f : A →* B} (hf : Function.Injective f) (p : ℕ) (X J : Subgroup A) :
    Type167 p (X.map f) (J.map f) ↔ Type167 p X J := by
  unfold Type167
  simp only [catalogIs_pSimple_map_iff hf]

theorem type167J_map_iff {f : A →* B} (hf : Function.Injective f) (p : ℕ) (J : Subgroup A) :
    Type167J p (J.map f) ↔ Type167J p J := by
  unfold Type167J
  simp only [catalogIs_pSimple_map_iff hf]

theorem isChevSimple_pSimple_map_iff {f : A →* B} (hf : Function.Injective f) (r p : ℕ) (X : Subgroup A) :
    IsChevSimple r (PSimple p (X.map f)) ↔ IsChevSimple r (PSimple p X) := by
  unfold IsChevSimple
  simp only [catalogIs_pSimple_map_iff hf]

theorem pRank_map_eq {f : A →* B} (hf : Function.Injective f) (p : ℕ) (X : Subgroup A) :
    CFSG.Open.pRank p (X.map f) = CFSG.Open.pRank p X := by
  unfold CFSG.Open.pRank
  congr 1
  ext k
  constructor
  · rintro ⟨E, hE, hEA, hc⟩
    have hEm : (E.comap f).map f = E :=
      Subgroup.map_comap_eq_self (fun b hb => MonoidHom.mem_range.2 (by
        obtain ⟨a, _, ha⟩ := Subgroup.mem_map.1 (hE hb)
        exact ⟨a, ha⟩))
    refine ⟨E.comap f, fun a ha => (Subgroup.mem_map_iff_mem hf).1 (hE (Subgroup.mem_comap.1 ha)), ?_, ?_⟩
    · rw [← isElemAbelian_map_iff hf p, hEm]
      exact hEA
    · calc Nat.card (E.comap f) = Nat.card ((E.comap f).map f) := (Subgroup.card_map_of_injective hf).symm
        _ = p ^ k := by rw [hEm]; exact hc
  · rintro ⟨E, hE, hEA, hc⟩
    exact ⟨E.map f, Subgroup.map_mono hE, (isElemAbelian_map_iff hf p E).2 hEA,
      by rw [Subgroup.card_map_of_injective hf]; exact hc⟩

end CFSG.LocalAnalysis.GLTheoremA.T123C

end
