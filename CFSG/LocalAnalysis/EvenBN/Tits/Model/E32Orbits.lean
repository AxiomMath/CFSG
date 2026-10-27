module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.E32
public import Certificates.Certificate27581

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Model

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherSecFour
  Certificates.TitsAschbacherE32
open CFSG.Quasithin (tπ twoF4H twoF4N)

@[expose] def IsLong (x : Equiv.Perm (Fin 1755)) : Prop := ∃ d ∈ titsD, d * titsZ * d⁻¹ = x

@[expose] def IsShort (x : Equiv.Perm (Fin 1755)) : Prop := ∃ d ∈ titsD, d * titsTInv * d⁻¹ = x

theorem isLong_titsZ : IsLong titsZ :=
  ⟨1, one_mem _, by group⟩

theorem IsLong.conj
    {x a : Equiv.Perm (Fin 1755)} (hx : IsLong x) (ha : a ∈ titsA) : IsLong (a * x * a⁻¹) := by
  obtain ⟨d, hd, rfl⟩ := hx
  obtain ⟨d', hd', h⟩ := exists_titsD_conj_titsZ (mul_mem ha (titsD_le_titsA hd))
  exact ⟨d', hd', by rw [h]; group⟩

theorem IsShort.conj
    {x a : Equiv.Perm (Fin 1755)} (hx : IsShort x) (ha : a ∈ titsA) : IsShort (a * x * a⁻¹) := by
  obtain ⟨d, hd, rfl⟩ := hx
  obtain ⟨d', hd', h⟩ := exists_titsD_conj_titsTInv (mul_mem ha (titsD_le_titsA hd))
  exact ⟨d', hd', by rw [h]; group⟩

theorem not_isLong_of_isShort
    {x : Equiv.Perm (Fin 1755)} (hx : IsShort x) : ¬ IsLong x := by
  rintro ⟨d, hd, rfl⟩
  obtain ⟨d', hd', h⟩ := hx
  apply titsA_conj_titsZ_ne_titsTInv (a := d'⁻¹ * d) (titsD_le_titsA (mul_mem (inv_mem hd') hd))
  calc d'⁻¹ * d * titsZ * (d'⁻¹ * d)⁻¹ = d'⁻¹ * (d * titsZ * d⁻¹) * d' := by group
    _ = d'⁻¹ * (d' * titsTInv * d'⁻¹) * d' := by rw [h]
    _ = titsTInv := by group

theorem IsLong.ne_one
    {x : Equiv.Perm (Fin 1755)} (hx : IsLong x) : x ≠ 1 := by
  obtain ⟨d, -, rfl⟩ := hx
  intro h
  apply titsZ_ne_one
  calc titsZ = d⁻¹ * (d * titsZ * d⁻¹) * d := by group
    _ = 1 := by rw [h]; group

theorem IsShort.ne_one
    {x : Equiv.Perm (Fin 1755)} (hx : IsShort x) : x ≠ 1 := by
  obtain ⟨d, -, rfl⟩ := hx
  intro h
  apply titsTInv_ne_one
  calc titsTInv = d⁻¹ * (d * titsTInv * d⁻¹) * d := by group
    _ = 1 := by rw [h]; group

theorem conj_eq_of_conjToA {g x y : Array ℕ} {G X Y : Equiv.Perm (Fin 1755)} (hg : Rep 1755 g G)
    (hx : Rep 1755 x X) (hy : Rep 1755 y Y) (h : conjToA g x y = true) : G * X * G⁻¹ = Y := by
  have e := eq_of_eqA (rep_compA hg hx) (rep_compA hy hg) h
  rw [e, mul_inv_cancel_right]

theorem mem_normalizer_closure {M : Type*} [Group M] [Finite M] {S : Set M} {g : M}
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ closure S) : g ∈ normalizer (closure S : Set M) := by
  apply CFSG.Quasithin.mem_normalizer_of_forall_conj_mem_f4
  intro x hx
  have hle : closure S ≤ (closure S).comap (MulAut.conj g).toMonoidHom := by
    rw [closure_le]
    intro s hs
    simpa [MulAut.conj_apply] using h s hs
  simpa [MulAut.conj_apply] using hle hx

theorem ncard_image_range {f : ℕ → Equiv.Perm (Fin 1755)}
    (hf : ∀ a < 32, ∀ b < 32, f a = f b → a = b) (p : ℕ → Prop) [DecidablePred p] :
    {x | ∃ m < 32, p m ∧ f m = x}.ncard = ((Finset.range 32).filter p).card := by
  have e : {x | ∃ m < 32, p m ∧ f m = x} = (((Finset.range 32).filter p).image f :
      Set (Equiv.Perm (Fin 1755))) := by
    ext x
    simp [and_assoc]
  rw [e, Set.ncard_coe_finset, Finset.card_image_of_injOn]
  intro a ha b hb hab
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hb
  exact hf a ha.1 b hb.1 hab

theorem getD_mem_of_lt {α : Type*} {l : List α} {d : α} {n : ℕ} (h : n < l.length) :
    l.getD n d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem orbCheck_eq_true : orbCheck () = true :=
  Certificates.certificate27581

theorem orbCheck_parts :
    eOrbData.all (eOrbOK (eArrs ())) = true ∧
      fOrbData.all (fOrbOK (fArrs ()) (u10Arrs ())) = true ∧
      eGenData.all (fun e => eqA 1755 ((eArrs ()).getD e.1 #[])
        (compA 1755 ((eArrs ()).getD e.2.1 #[]) ((eArrs ()).getD e.2.2 #[]))) = true ∧
      mGens.all (fun g => fIdx.all fun i => (fArrs ()).any fun f => conjToA g (vA i) f) = true ∧
      mGens.all (fun g => [10, 11, 12].all fun i =>
        (u10Arrs ()).any fun u => conjToA g (vA i) u) = true ∧
      (u10Arrs ()).all (fun a => (u10Arrs ()).all fun b =>
        (u10Arrs ()).any (eqA 1755 (compA 1755 a b))) = true ∧
      (List.range 32).all (fun a => (List.range 32).all fun b =>
        a == b || !eqA 1755 ((fArrs ()).getD a #[]) ((fArrs ()).getD b #[])) = true ∧
      nLetters n0Word = true ∧ conjToA (nArr n0Word) titsTArr (vA 10) = true ∧
      fCommData.all (fun e => hLetters e.2.1 && hLetters e.2.2 &&
        eqA 1755 (compA 1755 (hArr e.2.1) (hArr e.2.2))
          (compA 1755 (compA 1755 (vA e.1) (hArr e.2.2)) (hArr e.2.1))) = true := by
  have h := orbCheck_eq_true
  unfold orbCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem eElt_injOn
    {a b : ℕ} (ha : a < 32) (hb : b < 32)
    (hab : eElt a = eElt b) : a = b := by
  by_contra hne
  have h := List.all_eq_true.1 (List.all_eq_true.1 genCheck_parts.2.2.2.2.2 a
    (List.mem_range.2 ha)) b (List.mem_range.2 hb)
  rw [beq_eq_false_iff_ne.2 hne, Bool.false_or, Bool.not_eq_true'] at h
  have ra := rep_eArrs ha
  have rb := rep_eArrs hb
  rw [eArrs_getD ha] at ra
  rw [eArrs_getD hb] at rb
  rw [(eqA_iff ra rb).2 hab] at h
  exact absurd h (by decide)

theorem fElt_injOn
    {a b : ℕ} (ha : a < 32) (hb : b < 32)
    (hab : fElt a = fElt b) : a = b := by
  by_contra hne
  have h := List.all_eq_true.1 (List.all_eq_true.1 orbCheck_parts.2.2.2.2.2.2.1 a
    (List.mem_range.2 ha)) b (List.mem_range.2 hb)
  rw [beq_eq_false_iff_ne.2 hne, Bool.false_or, Bool.not_eq_true'] at h
  rw [(eqA_iff (rep_fArrs ha) (rep_fArrs hb)).2 hab] at h
  exact absurd h (by decide)

theorem card_parrottF
    : Nat.card parrottF = 32 := by
  refine le_antisymm card_parrottF_le ?_
  let f : Fin 32 → parrottF := fun m => ⟨fElt m, fElt_mem m.2⟩
  have hf : Function.Injective f := fun a b hab =>
    Fin.ext (fElt_injOn a.2 b.2 (congrArg Subtype.val hab))
  simpa using Nat.card_le_card_of_injective f hf

theorem mem_parrottF_iff
    {x : Equiv.Perm (Fin 1755)} : x ∈ parrottF ↔ ∃ m < 32, fElt m = x := by
  refine ⟨fun hx => ?_, fun ⟨m, hm, h⟩ => h ▸ fElt_mem hm⟩
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hsub : (Set.range fun m : Fin 32 => fElt m) ⊆ (parrottF : Set _) \ {x} := by
    rintro _ ⟨m, rfl⟩
    exact ⟨fElt_mem m.2, hne m m.2⟩
  have hinj : Function.Injective fun m : Fin 32 => fElt m := fun a b hab =>
    Fin.ext (fElt_injOn a.2 b.2 hab)
  have h1 : (Set.range fun m : Fin 32 => fElt m).ncard = 32 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ, Nat.card_fin]
  have hF : (parrottF : Set (Equiv.Perm (Fin 1755))).ncard = 32 := by
    rw [← Nat.card_coe_set_eq]
    exact card_parrottF
  have h2 : ((parrottF : Set (Equiv.Perm (Fin 1755))) \ {x}).ncard = 31 := by
    rw [Set.ncard_sdiff_singleton_of_mem hx, hF]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

@[expose] noncomputable def u10Elt (m : ℕ) : Equiv.Perm (Fin 1755) :=
  ((u10Bits m).map parrottV).prod

theorem u10Bits_bound : ∀ m < 8, ∀ i ∈ u10Bits m, 10 ≤ i ∧ i ≤ 12 := by decide

theorem rep_u10Arrs {m : ℕ}
    (hm : m < 8) : Rep 1755 ((u10Arrs ()).getD m #[]) (u10Elt m) := by
  have e : (u10Arrs ()).getD m #[] = vProd (u10Bits m) := by simp [u10Arrs, hm]
  rw [e]
  exact rep_vProd fun i hi => by have := u10Bits_bound m hm i hi; omega

theorem exists_of_mem_u10Arrs
    {a : Array ℕ} (ha : a ∈ u10Arrs ()) : ∃ m < 8, Rep 1755 a (u10Elt m) := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
  have hm' := List.mem_range.1 hm
  refine ⟨m, hm', ?_⟩
  have := rep_u10Arrs hm'
  have e : (u10Arrs ()).getD m #[] = vProd (u10Bits m) := by simp [u10Arrs, hm']
  rwa [e] at this

theorem mem_parrottU_ten_iff
    {x : Equiv.Perm (Fin 1755)} :
    x ∈ parrottU 10 ↔ ∃ m < 8, u10Elt m = x := by
  constructor
  · intro hx
    have h1 : (1 : Equiv.Perm (Fin 1755)) ∈ {x | ∃ m < 8, u10Elt m = x} :=
      ⟨0, by norm_num, by rw [u10Elt, show u10Bits 0 = [] by decide]; simp⟩
    have hmul : ∀ a ∈ {x | ∃ m < 8, u10Elt m = x}, ∀ b ∈ {x | ∃ m < 8, u10Elt m = x},
        a * b ∈ {x | ∃ m < 8, u10Elt m = x} := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have h := List.any_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1
        orbCheck_parts.2.2.2.2.2.1 _ (getD_mem_of_lt (d := #[]) (by simpa [u10Arrs] using ha)))
        _ (getD_mem_of_lt (d := #[]) (by simpa [u10Arrs] using hb)))
      obtain ⟨c, hc, hce⟩ := h
      obtain ⟨m, hm, hcm⟩ := exists_of_mem_u10Arrs hc
      exact ⟨m, hm, (eq_of_eqA (rep_compA (rep_u10Arrs ha) (rep_u10Arrs hb)) hcm hce).symm⟩
    have hS : parrottV '' Set.Icc 10 12 ⊆ {x | ∃ m < 8, u10Elt m = x} := by
      rintro _ ⟨i, ⟨hi1, hi2⟩, rfl⟩
      have hi : i = 10 ∨ i = 11 ∨ i = 12 := by omega
      rcases hi with rfl | rfl | rfl
      · exact ⟨1, by norm_num, by rw [u10Elt, show u10Bits 1 = [10] by decide]; simp⟩
      · exact ⟨2, by norm_num, by rw [u10Elt, show u10Bits 2 = [11] by decide]; simp⟩
      · exact ⟨4, by norm_num, by rw [u10Elt, show u10Bits 4 = [12] by decide]; simp⟩
    exact closure_subset_of_mul_mem h1 hmul hS hx
  · rintro ⟨m, hm, rfl⟩
    exact prod_mem_parrottU (u10Bits_bound m hm)

@[expose] def eTag (m : ℕ) : ℕ := (eOrbData.getD (m - 1) (0, 0, [])).2.1

@[expose] def eWord (m : ℕ) : List ℕ := (eOrbData.getD (m - 1) (0, 0, [])).2.2

@[expose] def fTag (m : ℕ) : ℕ := (fOrbData.getD (m - 1) (0, 0, [])).2.1

@[expose] def fWord (m : ℕ) : List ℕ := (fOrbData.getD (m - 1) (0, 0, [])).2.2

theorem eOrb_mem {m : ℕ} (hm : m < 32) (h1 : 1 ≤ m) : (m, eTag m, eWord m) ∈ eOrbData := by
  have hlen : eOrbData.length = 31 := by decide
  have hfst : ∀ m < 32, 1 ≤ m → (eOrbData.getD (m - 1) (0, 0, [])).1 = m := by decide
  have e : (m, eTag m, eWord m) = eOrbData.getD (m - 1) (0, 0, []) :=
    Prod.ext (hfst m hm h1).symm rfl
  rw [e]
  exact getD_mem_of_lt (by omega)

theorem fOrb_mem {m : ℕ} (hm : m < 32) (h1 : 1 ≤ m) : (m, fTag m, fWord m) ∈ fOrbData := by
  have hlen : fOrbData.length = 31 := by decide
  have hfst : ∀ m < 32, 1 ≤ m → (fOrbData.getD (m - 1) (0, 0, [])).1 = m := by decide
  have e : (m, fTag m, fWord m) = fOrbData.getD (m - 1) (0, 0, []) :=
    Prod.ext (hfst m hm h1).symm rfl
  rw [e]
  exact getD_mem_of_lt (by omega)

theorem eTag_facts : (∀ m < 32, 1 ≤ m → (eTag m = 0 ↔ m = 16)) ∧ (∀ m < 32, eTag m ≤ 2) ∧
    ((Finset.range 32).filter fun m => 1 ≤ m ∧ eTag m = 1).card = 10 ∧
    ((Finset.range 32).filter fun m => 1 ≤ m ∧ eTag m = 2).card = 20 := by decide

theorem fTag_facts : (∀ m < 32, 1 ≤ m → 1 ≤ fTag m ∧ fTag m ≤ 3) ∧
    (∀ m < 32, 1 ≤ m → (fTag m = 1 ↔ m = 8 ∨ m = 16 ∨ m = 24)) ∧
    ((Finset.range 32).filter fun m => 1 ≤ m ∧ fTag m = 2).card = 4 ∧
    ((Finset.range 32).filter fun m => 1 ≤ m ∧ fTag m = 3).card = 24 := by decide

theorem elt_values : eElt 0 = 1 ∧ eElt 16 = parrottV 12 ∧ eElt 8 = parrottV 11 ∧
    eElt 4 = parrottV 10 ∧ eElt 2 = parrottV 9 ∧ fElt 0 = 1 ∧ fElt 16 = parrottV 12 ∧
    fElt 8 = parrottV 11 ∧ fElt 24 = parrottV 11 * parrottV 12 ∧ fElt 4 = parrottV 10 ∧
    fElt 2 = parrottV 9 := by
  have e1 : u8Bits 0 = [] ∧ u8Bits 16 = [12] ∧ u8Bits 8 = [11] ∧ u8Bits 4 = [10] ∧
      u8Bits 2 = [9] := by decide
  have e2 : fBits 0 = [] ∧ fBits 16 = [12] ∧ fBits 8 = [11] ∧ fBits 24 = [11, 12] ∧
      fBits 4 = [10] ∧ fBits 2 = [9] := by decide
  simp only [eElt, fElt, e1.1, e1.2.1, e1.2.2.1, e1.2.2.2.1, e1.2.2.2.2, e2.1, e2.2.1, e2.2.2.1,
    e2.2.2.2.1, e2.2.2.2.2.1, e2.2.2.2.2.2, List.map_nil, List.prod_nil, List.map_cons,
    List.prod_cons, mul_one, and_self]

theorem exists_conj_eElt
    {m : ℕ} (hm : m < 32)
    (h1 : 1 ≤ m) :
    (eTag m = 1 → ∃ h ∈ titsH, h * parrottV 11 * h⁻¹ = eElt m) ∧
      (eTag m = 2 → ∃ h ∈ titsH, h * parrottV 10 * h⁻¹ = eElt m) := by
  have hok := List.all_eq_true.1 orbCheck_parts.1 _ (eOrb_mem hm h1)
  unfold eOrbOK at hok
  dsimp only at hok
  rw [Bool.and_eq_true] at hok
  obtain ⟨hw, hc⟩ := hok
  obtain ⟨hrep, hH⟩ := rep_hElt hw
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · split_ifs at hc
    all_goals first
      | omega
      | exact ⟨_, hH, conj_eq_of_conjToA hrep (rep_vA (by norm_num)) (rep_eArrs hm) hc⟩
  · split_ifs at hc
    all_goals first
      | omega
      | exact ⟨_, hH, conj_eq_of_conjToA hrep (rep_vA (by norm_num)) (rep_eArrs hm) hc⟩

theorem exists_conj_fElt
    {m : ℕ} (hm : m < 32)
    (h1 : 1 ≤ m) :
    (fTag m = 1 → ∃ n ∈ titsN, n * parrottV 12 * n⁻¹ = fElt m) ∧
      (fTag m = 2 → ∃ n ∈ titsN, n * parrottV 10 * n⁻¹ = fElt m) ∧
      (fTag m = 3 → ∃ n ∈ titsN, n * parrottV 9 * n⁻¹ = fElt m) ∧
      (fElt m ∈ parrottU 10 ↔ fTag m ≤ 2) := by
  have hok := List.all_eq_true.1 orbCheck_parts.2.1 _ (fOrb_mem hm h1)
  unfold fOrbOK at hok
  dsimp only at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨hw, hc⟩, hu⟩ := hok
  have hrep := rep_nArr hw
  have hN := nArr_mem hw
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_, ?_⟩
  · split_ifs at hc
    all_goals first
      | omega
      | exact ⟨_, hN, conj_eq_of_conjToA hrep (rep_vA (by norm_num)) (rep_fArrs hm) hc⟩
  · split_ifs at hc
    all_goals first
      | omega
      | exact ⟨_, hN, conj_eq_of_conjToA hrep (rep_vA (by norm_num)) (rep_fArrs hm) hc⟩
  · split_ifs at hc
    all_goals first
      | omega
      | exact ⟨_, hN, conj_eq_of_conjToA hrep (rep_vA (by norm_num)) (rep_fArrs hm) hc⟩
  · rw [beq_iff_eq] at hu
    constructor
    · intro hU
      obtain ⟨k, hk, hke⟩ := mem_parrottU_ten_iff.1 hU
      have hany : (u10Arrs ()).any (eqA 1755 ((fArrs ()).getD m #[])) = true :=
        List.any_eq_true.2 ⟨_, getD_mem_of_lt (d := #[]) (by simpa [u10Arrs] using hk),
          (eqA_iff (rep_fArrs hm) (rep_u10Arrs hk)).2 hke.symm⟩
      rw [hany] at hu
      exact of_decide_eq_true hu.symm
    · intro ht
      rw [decide_eq_true ht] at hu
      obtain ⟨u, hu', hue⟩ := List.any_eq_true.1 hu
      obtain ⟨k, hk, huk⟩ := exists_of_mem_u10Arrs hu'
      rw [(eqA_iff (rep_fArrs hm) huk).1 hue]
      exact mem_parrottU_ten_iff.2 ⟨k, hk, rfl⟩

theorem parrottV_twelve_eq :
    parrottV 12 = titsZ :=
  parrottV_twelve

theorem isLong_parrottV_eleven :
    IsLong (parrottV 11) := by
  have ht : fTag 8 = 1 := by decide
  obtain ⟨n, hn, h⟩ := (exists_conj_fElt (m := 8) (by norm_num) (by norm_num)).1 ht
  rw [elt_values.2.2.2.2.2.2.2.1, parrottV_twelve_eq] at h
  exact ⟨n, titsN_le_titsD hn, h⟩

theorem isShort_parrottV_ten :
    IsShort (parrottV 10) :=
  ⟨_, titsN_le_titsD (nArr_mem orbCheck_parts.2.2.2.2.2.2.2.1),
    conj_eq_of_conjToA (rep_nArr orbCheck_parts.2.2.2.2.2.2.2.1) titsTInv_rep
      (rep_vA (by norm_num)) orbCheck_parts.2.2.2.2.2.2.2.2.1⟩

theorem isShort_parrottV_nine
    : IsShort (parrottV 9) := by
  have ht : eTag 2 = 2 := by decide
  obtain ⟨h, hh, he⟩ := (exists_conj_eElt (m := 2) (by norm_num) (by norm_num)).2 ht
  rw [elt_values.2.2.2.2.1] at he
  rw [← he]
  exact isShort_parrottV_ten.conj (titsD_le_titsA (titsH_le_titsD hh))

theorem tπ_mem_normalizer_hatE
    : tπ ∈ normalizer (hatE : Set (Equiv.Perm (Fin 1755))) :=
  twoF4H_le_normalizer_hatE CFSG.Quasithin.q_mem_extSub

theorem not_le_normalizer_of_card
    {X : Subgroup (Equiv.Perm (Fin 1755))} (hXD : X ≤ titsD) (hz : titsZ ∈ X)
    (hcard : Nat.card X = 32) : ¬ titsD ≤ normalizer (X : Set (Equiv.Perm (Fin 1755))) := by
  intro hle
  have hn : (X.subgroupOf titsD).Normal := by
    rw [normal_subgroupOf_iff hXD]
    intro h k hh hk
    exact (mem_normalizer_iff.1 (hle hk) h).1 hh
  have := titsD_simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (X.subgroupOf titsD) with h | h
  · have hmem : (⟨titsZ, titsZ_mem_titsD⟩ : titsD) ∈ X.subgroupOf titsD := mem_subgroupOf.2 hz
    rw [h, mem_bot] at hmem
    exact titsZ_ne_one (congrArg Subtype.val hmem)
  · have hDX : titsD ≤ X := fun x hx => by
      have : (⟨x, hx⟩ : titsD) ∈ X.subgroupOf titsD := h ▸ mem_top _
      exact mem_subgroupOf.1 this
    have h1 := Subgroup.card_le_of_le hDX
    rw [hcard, card_titsD] at h1
    omega

theorem titsD_inf_normalizer_hatE
    : titsD ⊓ normalizer (hatE : Set (Equiv.Perm (Fin 1755))) = titsH := by
  have hHle : titsH ≤ titsD ⊓ normalizer (hatE : Set (Equiv.Perm (Fin 1755))) :=
    le_inf titsH_le_titsD (CFSG.Quasithin.le_extSub.trans twoF4H_le_normalizer_hatE)
  refine (eq_of_coatom_le titsH_isCoatom titsH_le_titsD inf_le_left hHle fun h => ?_).symm
  exact not_le_normalizer_of_card (hatE_le_titsJ.trans titsJ_le_titsD) titsZ_mem_hatE
    card_hatE.2.2.2 (h ▸ inf_le_right)

theorem titsA_inf_normalizer_hatE
    : titsA ⊓ normalizer (hatE : Set (Equiv.Perm (Fin 1755))) = twoF4H := by
  apply le_antisymm
  · intro a ha
    obtain ⟨haA, haN⟩ := mem_inf.1 ha
    by_cases haD : a ∈ titsD
    · exact CFSG.Quasithin.le_extSub (titsD_inf_normalizer_hatE ▸ mem_inf.2 ⟨haD, haN⟩)
    · refine Or.inr (titsD_inf_normalizer_hatE ▸ mem_inf.2 ⟨mul_tπ_inv_mem_titsD haA haD, ?_⟩)
      exact mul_mem haN (inv_mem tπ_mem_normalizer_hatE)
  · exact le_inf twoF4H_le_titsA twoF4H_le_normalizer_hatE

theorem twoF4N_le_normalizer_parrottF
    : twoF4N ≤ normalizer (parrottF : Set (Equiv.Perm (Fin 1755))) := by
  have key : ∀ g ∈ mGens, ∀ G : Equiv.Perm (Fin 1755), Rep 1755 g G →
      G ∈ normalizer (parrottF : Set (Equiv.Perm (Fin 1755))) := by
    intro g hg G hG
    apply mem_normalizer_closure
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i ∈ fIdx := by
      simp only [fIdx, List.mem_cons, List.not_mem_nil, or_false]
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp
    obtain ⟨f, hf, hgf⟩ := List.any_eq_true.1 (List.all_eq_true.1
      (List.all_eq_true.1 orbCheck_parts.2.2.2.1 g hg) i hi')
    obtain ⟨m, hm, hfm⟩ := exists_of_mem_fArrs hf
    have hi12 : i < 13 := by rcases hi with rfl | rfl | rfl | rfl | rfl <;> norm_num
    rw [conj_eq_of_conjToA hG (rep_vA hi12) hfm hgf]
    exact fElt_mem hm
  have hN : titsN ≤ normalizer (parrottF : Set (Equiv.Perm (Fin 1755))) := by
    rw [titsN_eq_closure_chainGen, closure_le]
    rintro _ ⟨i, rfl⟩
    exact key _ (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 i.2, rfl⟩)) _
      (chainGen_N_rep i.2)
  have hπ : tπ ∈ normalizer (parrottF : Set (Equiv.Perm (Fin 1755))) :=
    key _ (List.mem_append_right _ (List.mem_singleton_self _)) _ CFSG.Quasithin.tπ_rep
  rintro x (hx | hx)
  · exact hN hx
  · have := mul_mem (hN hx) hπ
    simpa using this

theorem titsD_inf_normalizer_parrottF
    : titsD ⊓ normalizer (parrottF : Set (Equiv.Perm (Fin 1755))) = titsN := by
  have hNle : titsN ≤ titsD ⊓ normalizer (parrottF : Set (Equiv.Perm (Fin 1755))) :=
    le_inf titsN_le_titsD (CFSG.Quasithin.le_extSub.trans twoF4N_le_normalizer_parrottF)
  refine (eq_of_coatom_le titsN_isCoatom titsN_le_titsD inf_le_left hNle fun h => ?_).symm
  have hz : titsZ ∈ parrottF := by
    rw [← parrottV_twelve_eq]
    exact subset_closure ⟨12, by simp, rfl⟩
  exact not_le_normalizer_of_card parrottF_le_titsD hz card_parrottF (h ▸ inf_le_right)

theorem titsA_inf_normalizer_parrottF
    : titsA ⊓ normalizer (parrottF : Set (Equiv.Perm (Fin 1755))) = twoF4N := by
  apply le_antisymm
  · intro a ha
    obtain ⟨haA, haN⟩ := mem_inf.1 ha
    by_cases haD : a ∈ titsD
    · exact CFSG.Quasithin.le_extSub (titsD_inf_normalizer_parrottF ▸ mem_inf.2 ⟨haD, haN⟩)
    · refine Or.inr (titsD_inf_normalizer_parrottF ▸ mem_inf.2 ⟨mul_tπ_inv_mem_titsD haA haD, ?_⟩)
      exact mul_mem haN (inv_mem (twoF4N_le_normalizer_parrottF CFSG.Quasithin.q_mem_extSub))
  · exact le_inf twoF4N_le_titsA twoF4N_le_normalizer_parrottF

theorem twoF4N_le_normalizer_parrottU_ten
    : twoF4N ≤ normalizer (parrottU 10 : Set (Equiv.Perm (Fin 1755))) := by
  have key : ∀ g ∈ mGens, ∀ G : Equiv.Perm (Fin 1755), Rep 1755 g G →
      G ∈ normalizer (parrottU 10 : Set (Equiv.Perm (Fin 1755))) := by
    intro g hg G hG
    apply mem_normalizer_closure
    rintro _ ⟨i, ⟨hi1, hi2⟩, rfl⟩
    have hi' : i ∈ [10, 11, 12] := by
      have : i = 10 ∨ i = 11 ∨ i = 12 := by omega
      rcases this with rfl | rfl | rfl <;> simp
    obtain ⟨u, hu, hgu⟩ := List.any_eq_true.1 (List.all_eq_true.1
      (List.all_eq_true.1 orbCheck_parts.2.2.2.2.1 g hg) i hi')
    obtain ⟨m, hm, hum⟩ := exists_of_mem_u10Arrs hu
    rw [conj_eq_of_conjToA hG (rep_vA (by omega)) hum hgu]
    exact mem_parrottU_ten_iff.2 ⟨m, hm, rfl⟩
  have hN : titsN ≤ normalizer (parrottU 10 : Set (Equiv.Perm (Fin 1755))) := by
    rw [titsN_eq_closure_chainGen, closure_le]
    rintro _ ⟨i, rfl⟩
    exact key _ (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 i.2, rfl⟩)) _
      (chainGen_N_rep i.2)
  have hπ : tπ ∈ normalizer (parrottU 10 : Set (Equiv.Perm (Fin 1755))) :=
    key _ (List.mem_append_right _ (List.mem_singleton_self _)) _ CFSG.Quasithin.tπ_rep
  rintro x (hx | hx)
  · exact hN hx
  · have := mul_mem (hN hx) hπ
    simpa using this

theorem not_map_conj_hatE_eq_parrottF
    {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsA) :
    hatE.map (MulAut.conj a).toMonoidHom ≠ parrottF := by
  intro h
  have hmap : ∀ b ∈ twoF4H, a * b * a⁻¹ ∈ twoF4N := by
    intro b hb
    rw [← titsA_inf_normalizer_hatE] at hb
    obtain ⟨hbA, hbN⟩ := mem_inf.1 hb
    rw [← titsA_inf_normalizer_parrottF]
    refine mem_inf.2 ⟨mul_mem (mul_mem ha hbA) (inv_mem ha), ?_⟩
    rw [mem_normalizer_iff]
    intro y
    rw [← h, mem_map_conj_iff, mem_map_conj_iff, (mem_normalizer_iff.1 hbN) (a⁻¹ * y * a)]
    have e : a⁻¹ * (a * b * a⁻¹ * y * (a * b * a⁻¹)⁻¹) * a = b * (a⁻¹ * y * a) * b⁻¹ := by group
    rw [e]
  let f : twoF4H → twoF4N := fun b => ⟨a * b * a⁻¹, hmap b b.2⟩
  have hf : Function.Injective f := fun b c hbc => by
    have h1 : a * (b : Equiv.Perm (Fin 1755)) * a⁻¹ = a * c * a⁻¹ := congrArg Subtype.val hbc
    exact Subtype.ext (by simpa using h1)
  have h1 := Nat.card_le_card_of_injective f hf
  rw [card_twoF4H, card_twoF4N.1] at h1
  omega

end CFSG.LocalAnalysis.EvenBN.Tits.Model
