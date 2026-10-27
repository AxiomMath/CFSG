module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeGlueFacts
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HePres
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step46

public section

namespace CFSG.ComponentClassification.AS81.HeTri

open Subgroup CFSG.Monster.B.Co2 CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.Hexa CFSG.ComponentClassification.AS81.HePres.Native
open CFSG.ComponentClassification.AS81.HePres

theorem map_freeGroup_lift {H K : Type*} [Group H] [Group K] (θ : H →* K) {k : ℕ} (f : Fin k → H)
    (x : FreeGroup (Fin k)) : θ (FreeGroup.lift f x) = FreeGroup.lift (fun i => θ (f i)) x :=
  FreeGroup.lift_unique (θ.comp (FreeGroup.lift f)) (fun i => by simp)

theorem lift_eq_of_model {H K : Type*} [Group H] [Group K] {L : Subgroup H} (θ : ↥L →* K)
    {k : ℕ} {g : Fin k → K} {h : Fin k → H} {w : List (Fin k × Bool)}
    (hL : ∀ l ∈ w, h l.1 ∈ L) (hg : ∀ l ∈ w, ∀ hl : h l.1 ∈ L, g l.1 = θ ⟨h l.1, hl⟩) :
    ∃ hw : FreeGroup.lift h (FreeGroup.mk w) ∈ L,
      FreeGroup.lift g (FreeGroup.mk w) = θ ⟨FreeGroup.lift h (FreeGroup.mk w), hw⟩ := by
  classical
  set h' : Fin k → ↥L := fun i => if hi : h i ∈ L then ⟨h i, hi⟩ else 1 with hh'
  have hh : ∀ (l) (hl : l ∈ w), h' l.1 = ⟨h l.1, hL l hl⟩ := fun l hl => by simp [hh', hL l hl]
  have h1 : FreeGroup.lift g (FreeGroup.mk w) =
      FreeGroup.lift (fun i => θ (h' i)) (FreeGroup.mk w) := by
    refine HePres.lift_mk_congr fun l hl => ?_
    rw [hg l hl (hL l hl), hh l hl]
  have h2 : ((FreeGroup.lift h' (FreeGroup.mk w) : ↥L) : H) =
      FreeGroup.lift h (FreeGroup.mk w) := by
    rw [← L.coe_subtype, map_freeGroup_lift]
    refine HePres.lift_mk_congr fun l hl => ?_
    rw [hh l hl]
    rfl
  refine ⟨h2 ▸ (FreeGroup.lift h' (FreeGroup.mk w)).2, ?_⟩
  rw [h1, ← map_freeGroup_lift]
  congr 1
  exact Subtype.ext h2

theorem lift_eq_one_of_model {H K : Type*} [Group H] [Group K] {L : Subgroup H} (θ : ↥L →* K)
    {k : ℕ} {g : Fin k → K} {h : Fin k → H} {r : List (Fin k × Bool)}
    (hr : FreeGroup.lift h (FreeGroup.mk r) = 1) (hL : ∀ l ∈ r, h l.1 ∈ L)
    (hg : ∀ l ∈ r, ∀ hl : h l.1 ∈ L, g l.1 = θ ⟨h l.1, hl⟩) :
    FreeGroup.lift g (FreeGroup.mk r) = 1 := by
  obtain ⟨hw, he⟩ := lift_eq_of_model θ hL hg
  rw [he, show (⟨FreeGroup.lift h (FreeGroup.mk r), hw⟩ : ↥L) = 1 from Subtype.ext hr, map_one]

theorem range_le_of_closure {H K P : Type*} [Group H] [Group K] [Group P] {L : Subgroup H}
    (θ : ↥L →* K) {S : Set H} (hLS : L ≤ closure S) (Φ : P →* K)
    (hS : ∀ x ∈ S, ∃ hx : x ∈ L, θ ⟨x, hx⟩ ∈ Φ.range) : θ.range ≤ Φ.range := by
  set L' := (Φ.range.comap θ).map L.subtype with hL'
  have hSL : closure S ≤ L' := by
    rw [closure_le]
    intro x hx
    obtain ⟨hxL, hxr⟩ := hS x hx
    exact ⟨⟨x, hxL⟩, hxr, rfl⟩
  rintro _ ⟨y, rfl⟩
  obtain ⟨y', hy', hyy⟩ := hSL (hLS y.2)
  have : y' = y := Subtype.ext hyy
  rw [← this]
  exact hy'

variable {G : Type} [Group G] {E F S₁ : Subgroup G} {z : G}

noncomputable def glueHom {X : Subgroup G} (fC : ↥hePC ≃* ↥(centralizer ({z} : Set G)))
    (fX : ↥heN0 ≃* ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G))))
    (hXP : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heP12 ↔ (fX n : G) ∈ iX z X)
    {P : Subgroup (Equiv.Perm (Fin 32))} (hPC : P ≤ hePC)
    (hPX : ∀ n : ↥hePC, (n : Equiv.Perm (Fin 32)) ∈ P → (fC n : G) ∈ iX z X) :
    ↥P →* ↥heP12 :=
  (heN0.subtype.comp (fX.symm.toMonoidHom.comp
    (((centralizer ({z} : Set G)).subtype.comp (fC.toMonoidHom.comp (inclusion hPC))).codRestrict
      (AS76b.oUpperTwoPrime (normalizer (X : Set G)))
      fun x => oUpper_mono' inf_le_right (hPX _ x.2)))).codRestrict heP12 fun x =>
    (hXP _).mpr (by simpa using hPX _ x.2)

section GlueHom

variable {X : Subgroup G} (fC : ↥hePC ≃* ↥(centralizer ({z} : Set G)))
    (fX : ↥heN0 ≃* ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G))))
    (hXP : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heP12 ↔ (fX n : G) ∈ iX z X)
    {P : Subgroup (Equiv.Perm (Fin 32))} (hPC : P ≤ hePC)
    (hPX : ∀ n : ↥hePC, (n : Equiv.Perm (Fin 32)) ∈ P → (fC n : G) ∈ iX z X)

theorem fX_glueHom (x : ↥P) {m : Equiv.Perm (Fin 64)} (hm : m ∈ heN0)
    (h : (glueHom fC fX hXP hPC hPX x : Equiv.Perm (Fin 64)) = m) :
    (fX ⟨m, hm⟩ : G) = (fC ⟨x, hPC x.2⟩ : G) := by
  subst h
  have : (⟨_, hm⟩ : ↥heN0) =
      fX.symm ⟨fC ⟨x, hPC x.2⟩, oUpper_mono' inf_le_right (hPX _ x.2)⟩ := Subtype.ext rfl
  rw [this, MulEquiv.apply_symm_apply]

theorem glueHom_injective : Function.Injective (glueHom fC fX hXP hPC hPX) := by
  intro x y hxy
  have h1 := fX_glueHom fC fX hXP hPC hPX x (glueHom fC fX hXP hPC hPX x).2.1 rfl
  rw [hxy] at h1
  rw [fX_glueHom fC fX hXP hPC hPX y (glueHom fC fX hXP hPC hPX y).2.1 rfl] at h1
  have h2 := fC.injective (Subtype.ext h1)
  exact Subtype.ext (congrArg Subtype.val h2).symm

theorem glueHom_mem_heB0
    (hCB : ∀ n : ↥hePC, (n : Equiv.Perm (Fin 32)) ∈ heBC ↔ (fC n : G) ∈ S₁)
    (hXB : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heB0 ↔ (fX n : G) ∈ S₁) (x : ↥P)
    (hx : (x : Equiv.Perm (Fin 32)) ∈ heBC) :
    (glueHom fC fX hXP hPC hPX x : Equiv.Perm (Fin 64)) ∈ heB0 := by
  have h1 := fX_glueHom fC fX hXP hPC hPX x (glueHom fC fX hXP hPC hPX x).2.1 rfl
  refine (hXB ⟨_, (glueHom fC fX hXP hPC hPX x).2.1⟩).mpr ?_
  rw [h1]
  exact (hCB _).mp hx

end GlueHom

section Equiv23

variable (fE : ↥heN0 ≃* ↥(AS76b.oUpperTwoPrime (normalizer (E : Set G))))
    (fF : ↥heN0 ≃* ↥(AS76b.oUpperTwoPrime (normalizer (F : Set G))))
    (hE23 : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heP23 ↔
      (fE n : G) ∈ AS76b.oUpperTwoPrime (normalizer (F : Set G)))
    (hF23 : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heP23 ↔
      (fF n : G) ∈ AS76b.oUpperTwoPrime (normalizer (E : Set G)))
    (h23 : heP23 ≤ heN0)

noncomputable def glueHom23 : ↥heP23 →* ↥heP23 :=
  (heN0.subtype.comp (fF.symm.toMonoidHom.comp
    (((AS76b.oUpperTwoPrime (normalizer (E : Set G))).subtype.comp
      (fE.toMonoidHom.comp (inclusion h23))).codRestrict
      (AS76b.oUpperTwoPrime (normalizer (F : Set G))) fun y => (hE23 _).mp y.2))).codRestrict
    heP23 fun y => (hF23 _).mpr (by simp)

theorem fF_glueHom23 (y : ↥heP23) {m : Equiv.Perm (Fin 64)} (hm : m ∈ heN0)
    (h : (glueHom23 fE fF hE23 hF23 h23 y : Equiv.Perm (Fin 64)) = m) :
    (fF ⟨m, hm⟩ : G) = (fE ⟨y, h23 y.2⟩ : G) := by
  subst h
  have : (⟨_, hm⟩ : ↥heN0) = fF.symm ⟨fE ⟨y, h23 y.2⟩, (hE23 _).mp y.2⟩ := Subtype.ext rfl
  rw [this, MulEquiv.apply_symm_apply]

theorem glueHom23_injective : Function.Injective (glueHom23 fE fF hE23 hF23 h23) := by
  intro x y hxy
  have h1 := fF_glueHom23 fE fF hE23 hF23 h23 x (h23 (glueHom23 fE fF hE23 hF23 h23 x).2) rfl
  rw [hxy] at h1
  rw [fF_glueHom23 fE fF hE23 hF23 h23 y (h23 (glueHom23 fE fF hE23 hF23 h23 y).2) rfl] at h1
  have h2 := fE.injective (Subtype.ext h1)
  exact Subtype.ext (congrArg Subtype.val h2).symm

noncomputable def glueEquiv23 : ↥heP23 ≃* ↥heP23 :=
  MulEquiv.ofBijective (glueHom23 fE fF hE23 hF23 h23)
    (Finite.injective_iff_bijective.mp (glueHom23_injective fE fF hE23 hF23 h23))

theorem fF_glueEquiv23 (y : ↥heP23) {m : Equiv.Perm (Fin 64)} (hm : m ∈ heN0)
    (h : (glueEquiv23 fE fF hE23 hF23 h23 y : Equiv.Perm (Fin 64)) = m) :
    (fF ⟨m, hm⟩ : G) = (fE ⟨y, h23 y.2⟩ : G) :=
  fF_glueHom23 fE fF hE23 hF23 h23 y hm h

end Equiv23

theorem exists_hePiHom (hm : heModelCheck = true)
    (hg : heGlueCheck = true) (hF : HexaFacts) (s : Bool)
    (fC : ↥hePC ≃* ↥(centralizer ({z} : Set G)))
    (fE : ↥heN0 ≃* ↥(AS76b.oUpperTwoPrime (normalizer (E : Set G))))
    (fF : ↥heN0 ≃* ↥(AS76b.oUpperTwoPrime (normalizer (F : Set G))))
    (hCz : ∀ n : ↥hePC, (n : Equiv.Perm (Fin 32)) = heTC ↔ (fC n : G) = z)
    (hCB : ∀ n : ↥hePC, (n : Equiv.Perm (Fin 32)) ∈ heBC ↔ (fC n : G) ∈ S₁)
    (hCE : ∀ n : ↥hePC, (n : Equiv.Perm (Fin 32)) ∈ heP12C s ↔ (fC n : G) ∈ iX z E)
    (hCF : ∀ n : ↥hePC, (n : Equiv.Perm (Fin 32)) ∈ heP12C (!s) ↔ (fC n : G) ∈ iX z F)
    (hEP : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heP12 ↔ (fE n : G) ∈ iX z E)
    (hEB : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heB0 ↔ (fE n : G) ∈ S₁)
    (hE23 : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heP23 ↔
      (fE n : G) ∈ AS76b.oUpperTwoPrime (normalizer (F : Set G)))
    (hFP : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heP12 ↔ (fF n : G) ∈ iX z F)
    (hFB : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heB0 ↔ (fF n : G) ∈ S₁)
    (hF23 : ∀ n : ↥heN0, (n : Equiv.Perm (Fin 64)) ∈ heP23 ↔
      (fF n : G) ∈ AS76b.oUpperTwoPrime (normalizer (E : Set G))) :
    ∃ (Φ : HePi →* G) (p : ↥heN0),
      centralizer ({z} : Set G) ≤ Φ.range ∧
      AS76b.oUpperTwoPrime (normalizer (E : Set G)) ≤ Φ.range ∧ Φ hePiZ = z ∧
      (∀ k : Fin 8, ∀ hk : (k : ℕ) ≤ 5,
        Φ (PresentedGroup.of k) = fC ⟨piC s k, piC_mem hm hg s hk⟩) ∧
      ∀ w : List (Fin 8 × Bool), (∀ l ∈ w, (l.1 : ℕ) ≤ 4 ∨ (l.1 : ℕ) = 6 ∨ (l.1 : ℕ) = 7) →
        ∃ hw : FreeGroup.lift (fun i : Fin 8 => piE i) (FreeGroup.mk w) ∈ heN0,
          Φ (PresentedGroup.mk _ (FreeGroup.mk w)) = (fE (p * ⟨_, hw⟩ * p⁻¹) : G) := by
  classical
  have hBC_le : ∀ s, heBC ≤ heP12C s := BC_le_P_of hm
  have hPC : ∀ s, heP12C s ≤ hePC := P_le_PC_of hm
  have h23 : heP23 ≤ heN0 := heP23_le_heN0 hm
  have hB023 : heB0 ≤ heP23 := heB0_le_heP23 hm hF
  set φ := glueHom fC fE hEP (hPC s) fun n hn => (hCE n).mp hn with hφ
  set φ' := glueHom fC fF hFP (hPC (!s)) fun n hn => (hCF n).mp hn with hφ'
  set u := glueEquiv23 fE fF hE23 hF23 h23 with hu
  have hinj : ∀ {a b : Equiv.Perm (Fin 64)} (ha : a ∈ heN0) (hb : b ∈ heN0),
      (fF ⟨a, ha⟩ : G) = (fF ⟨b, hb⟩ : G) → a = b := fun ha hb h =>
    congrArg Subtype.val (fF.injective (Subtype.ext h))
  obtain ⟨p, hpB, q, hq, h1, h2, h3⟩ := exists_conj_glue hm hg hF s φ
    (glueHom_injective fC fE hEP (hPC s) _)
    (fun x hx => glueHom_mem_heB0 fC fE hEP (hPC s) _ hCB hEB x hx) φ'
    (glueHom_injective fC fF hFP (hPC (!s)) _)
    (fun x hx => glueHom_mem_heB0 fC fF hFP (hPC (!s)) _ hCB hFB x hx) u
    (fun x x' y hxx' _ hy => by
      refine hinj ((u y).2 |> h23) (φ' x').2.1 ?_
      rw [fF_glueEquiv23 fE fF hE23 hF23 h23 y _ rfl,
        fX_glueHom fC fE hEP (hPC s) _ x (h23 y.2) hy.symm,
        fX_glueHom fC fF hFP (hPC (!s)) _ x' (φ' x').2.1 rfl]
      congr 2
      exact Subtype.ext hxx')
  have hpN : p ∈ heN0 := h23 (hB023 hpB)
  have hqN : q ∈ heN0 := hq.1.1
  set pN : ↥heN0 := ⟨p, hpN⟩ with hpN'
  set qN : ↥heN0 := ⟨q, hqN⟩ with hqN'
  have hlt : ∀ i : Fin 8, ¬ (i : ℕ) ≤ 5 → (i : ℕ) = 6 ∨ (i : ℕ) = 7 := fun i hi => by
    have := i.isLt
    omega
  set g : Fin 8 → G := fun i => if hi : (i : ℕ) ≤ 5 then (fC ⟨piC s i, piC_mem hm hg s hi⟩ : G)
    else (fE (pN * ⟨piE i, piE_mem hm hg (Or.inr (hlt i hi))⟩ * pN⁻¹) : G) with hgd
  have gC : ∀ (i : Fin 8) (hi : (i : ℕ) ≤ 5), g i = (fC ⟨piC s i, piC_mem hm hg s hi⟩ : G) :=
    fun i hi => by simp only [hgd, hi, dite_true]
  have gE : ∀ (i : Fin 8) (hi : (i : ℕ) ≤ 4 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7),
      g i = (fE (pN * ⟨piE i, piE_mem hm hg hi⟩ * pN⁻¹) : G) := by
    intro i hi
    have hmN : p * piE i * p⁻¹ ∈ heN0 :=
      heN0.mul_mem (heN0.mul_mem hpN (piE_mem hm hg hi)) (heN0.inv_mem hpN)
    by_cases h5 : (i : ℕ) ≤ 5
    · have hi4 : (i : ℕ) ≤ 4 := by omega
      have hmem : piC s i ∈ heP12C s := by
        rcases Nat.lt_or_ge (i : ℕ) 4 with h | h
        · exact hBC_le s (piC_mem_heBC hm hg s h)
        · rw [show (i : ℕ) = 4 by omega]
          exact piC_mem_P hm hg s
      rw [gC i h5]
      exact (fX_glueHom fC fE hEP (hPC s) _ ⟨piC s i, hmem⟩ hmN
        (h1 i hi4 ⟨piC s i, hmem⟩ rfl)).symm
    · simp only [hgd, h5, dite_false]
  have gF : ∀ (i : Fin 8) (hi : (i : ℕ) < 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7),
      g i = (fF (qN * ⟨piF i, piF_mem hm hg hi⟩ * qN⁻¹) : G) := by
    intro i hi
    have hmN : q * piF i * q⁻¹ ∈ heN0 :=
      heN0.mul_mem (heN0.mul_mem hqN (piF_mem hm hg hi)) (heN0.inv_mem hqN)
    by_cases h5 : (i : ℕ) ≤ 5
    · have hmem : piC s i ∈ heP12C (!s) := by
        rcases hi with h | h | h | h
        · exact hBC_le (!s) (piC_mem_heBC hm hg s h)
        · rw [h]
          exact piC_mem_P' hm hg s
        · omega
        · omega
      have hne : (i : ℕ) ≠ 4 := by omega
      rw [gC i h5]
      exact (fX_glueHom fC fF hFP (hPC (!s)) _ ⟨piC s i, hmem⟩ hmN
        (h2 i h5 hne ⟨piC s i, hmem⟩ rfl)).symm
    · have h67 := hlt i h5
      rw [gE i (Or.inr h67)]
      have hy : p * piE i * p⁻¹ ∈ heP23 := heP23.mul_mem
        (heP23.mul_mem (hB023 hpB) (piE_mem_heP23 hm hg h67)) (heP23.inv_mem (hB023 hpB))
      exact (fF_glueEquiv23 fE fF hE23 hF23 h23 ⟨_, hy⟩ hmN (h3 i h67 ⟨_, hy⟩ rfl)).symm
  set θC : ↥hePC →* G := (centralizer ({z} : Set G)).subtype.comp fC.toMonoidHom with hθC
  set θE : ↥heN0 →* G := (AS76b.oUpperTwoPrime (normalizer (E : Set G))).subtype.comp
    (fE.toMonoidHom.comp (MulAut.conj pN).toMonoidHom) with hθE
  set θF : ↥heN0 →* G := (AS76b.oUpperTwoPrime (normalizer (F : Set G))).subtype.comp
    (fF.toMonoidHom.comp (MulAut.conj qN).toMonoidHom) with hθF
  have hrel : ∀ r ∈ hePiRels, FreeGroup.lift g (FreeGroup.mk r) = 1 := by
    intro r hr
    rcases hePiRels_mem r hr with hC | hE | hF
    · have hl5 : ∀ l ∈ r, (l.1 : ℕ) ≤ 5 := fun l hl => by
        have h67 := hePiRelsC_letters r hC l hl
        have := l.1.isLt
        have h6 : (l.1 : ℕ) ≠ 6 := fun h => h67.1 (Fin.ext h)
        have h7 : (l.1 : ℕ) ≠ 7 := fun h => h67.2 (Fin.ext h)
        omega
      exact lift_eq_one_of_model θC (h := fun i : Fin 8 => piC s i) (hePiC_rels s r hC)
        (fun l hl => piC_mem hm hg s (hl5 l hl)) fun l hl _ => gC l.1 (hl5 l hl)
    · have hlE : ∀ l ∈ r, (l.1 : ℕ) ≤ 4 ∨ (l.1 : ℕ) = 6 ∨ (l.1 : ℕ) = 7 := fun l hl => by
        have h5 := hePiRelsE_letters r hE l hl
        have := l.1.isLt
        have h5' : (l.1 : ℕ) ≠ 5 := fun h => h5 (Fin.ext h)
        omega
      exact lift_eq_one_of_model θE (h := fun i : Fin 8 => piE i) (hePiE_rels r hE)
        (fun l hl => piE_mem hm hg (hlE l hl)) fun l hl _ => gE l.1 (hlE l hl)
    · have hlF : ∀ l ∈ r, (l.1 : ℕ) < 4 ∨ (l.1 : ℕ) = 5 ∨ (l.1 : ℕ) = 6 ∨ (l.1 : ℕ) = 7 :=
        fun l hl => by
          have h4 := hePiRelsF_letters r hF l hl
          have := l.1.isLt
          have h4' : (l.1 : ℕ) ≠ 4 := fun h => h4 (Fin.ext h)
          omega
      exact lift_eq_one_of_model θF (h := fun i : Fin 8 => piF i) (hePiF_rels r hF)
        (fun l hl => piF_mem hm hg (hlF l hl)) fun l hl _ => gF l.1 (hlF l hl)
  set Φ := hePiLift g hrel with hΦ
  refine ⟨Φ, pN, ?_, ?_, ?_, fun k hk => ?_, fun w hw => ?_⟩
  ·
    intro y hy
    have hθ := range_le_of_closure θC (hePC_le_closure hg s) Φ (by
      rintro x ⟨k, hk, rfl⟩
      refine ⟨piC_mem hm hg s hk, PresentedGroup.of ⟨k, by omega⟩, ?_⟩
      rw [hΦ, hePiLift_of]
      exact gC ⟨k, by omega⟩ hk)
    exact hθ ⟨fC.symm ⟨y, hy⟩, by simp [hθC]⟩
  ·
    intro y hy
    have hθ := range_le_of_closure θE (heN0_le_closure hg) Φ (by
      rintro x ⟨k, hk, rfl⟩
      have hk8 : k < 8 := by omega
      refine ⟨piE_mem hm hg hk, PresentedGroup.of ⟨k, hk8⟩, ?_⟩
      rw [hΦ, hePiLift_of]
      exact gE ⟨k, hk8⟩ hk)
    refine hθ ⟨pN⁻¹ * fE.symm ⟨y, hy⟩ * pN, ?_⟩
    simp [hθE, mul_assoc]
  ·
    rw [hΦ, hePiLift_z, gC 1 (by decide), gC 2 (by decide), ← coe_mul, ← coe_mul, ← coe_mul,
      ← map_mul, ← map_mul, ← map_mul]
    refine (hCz _).mp ?_
    simp only [coe_mul]
    exact piC_z hg s
  · rw [hΦ, hePiLift_of]
    exact gC k hk
  · obtain ⟨hw', he⟩ := lift_eq_of_model θE (h := fun i : Fin 8 => piE i) (g := g) (w := w)
      (fun l hl => piE_mem hm hg (hw l hl)) fun l hl _ => gE l.1 (hw l hl)
    refine ⟨hw', ?_⟩
    rw [hΦ, hePiLift_mk, he]
    rfl

end CFSG.ComponentClassification.AS81.HeTri
