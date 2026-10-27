
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData

@[expose] public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover

section Arrays

variable {n : ℕ}

theorem permOfArr_eq_of_rep {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n t g) :
    permOfArr n t = g := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j :=
    ⟨fun i hi => h.lt hi, fun i hi j hj hij => by
      rw [h.apply hi, h.apply hj] at hij
      have := g.injective (Fin.ext hij)
      simpa using this⟩
  ext x
  rw [permOfArr, dite_eq_left hc]
  change t[(x : ℕ)]! = _
  exact h x

theorem getElem!_rawInvs' {S : Array (Array ℕ)} {j : ℕ} (hj : j < S.size) :
    (rawInvs n S)[j]! = invCand n S[j]! := by
  rw [rawInvs, getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos S j hj]

theorem size_pushWords (S : Array (Array ℕ)) (ws : List (List ℤ)) :
    (pushWords n S ws).size = S.size + ws.length := by
  induction ws generalizing S with
  | nil => simp [pushWords]
  | cons w ws ih =>
    rw [pushWords, ih, Array.size_push, List.length_cons]
    omega

theorem pushWords_getElem! (S : Array (Array ℕ)) (ws : List (List ℤ)) {i : ℕ}
    (hi : i < S.size) : (pushWords n S ws)[i]! = S[i]! := by
  induction ws generalizing S with
  | nil => rfl
  | cons w ws ih =>
    rw [pushWords, ih _ (by rw [Array.size_push]; omega), getElem!_pos _ i (by simp; omega),
      getElem!_pos S i hi, Array.getElem_push_lt]

theorem wordA_mem' {S : Array (Array ℕ)} {K : Subgroup (Equiv.Perm (Fin n))}
    (hS : ∀ h < S.size, Rep n S[h]! (permOfArr n S[h]!) ∧
      Rep n (rawInvs n S)[h]! (permOfArr n S[h]!)⁻¹ ∧ permOfArr n S[h]! ∈ K) :
    ∀ w : List ℤ, lettersOK S.size w = true →
      ∃ g ∈ K, Rep n (wordA n S (rawInvs n S) w) g
  | [], _ => ⟨1, K.one_mem, rep_idA⟩
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : lettersOK S.size w = true := by
      simpa [lettersOK, List.all_eq_true] using hw
    obtain ⟨g, hgK, hg⟩ := wordA_mem' hS w hw'
    have hlet := rep_letterA (gs := fun h => permOfArr n S[h]!) (j := S.size)
      (fun h hh => (hS h hh).1) (fun h hh => (hS h hh).2.1) ⟨hl0, hlj⟩
    refine ⟨_, K.mul_mem ?_ hgK, rep_compA hlet hg⟩
    by_cases hpos : decide (0 < l) = true
    · rw [ite_eq_left hpos]
      exact (hS _ (by omega)).2.2
    · rw [ite_eq_right hpos]
      exact K.inv_mem (hS _ (by omega)).2.2

end Arrays

section Chains

variable {n : ℕ} {hn : 1 ≤ n} {S : Array (Array ℕ)} {k : ℕ} {hk : k ≤ S.size}
  {base : List (Fin n)} {hb : base.Nodup} {W : Array (List ℤ)}

theorem chain_strong_spec
    (h : rawChainOK n (S.extract 0 k) S (base.map Fin.val).toArray W 4 = true) :
    ∀ j < S.size, Rep n S[j]! (permOfArr n S[j]!) ∧
      Rep n (rawInvs n S)[j]! (permOfArr n S[j]!)⁻¹ ∧
      permOfArr n S[j]! ∈ (RawSchreierDatum.ofArrays n hn S k hk base hb W).originalSubgroup := by
  intro j hj
  have hinv := (chainCheckFacts h).strong_inv j hj
  obtain ⟨h1, h2⟩ := rep_permOfArr hinv
  refine ⟨h1, h2, ?_⟩
  have hv := ofArrays_valid (hn := hn) (hk := hk) (hb := hb) (by norm_num : 0 < 4) h
  have hm := RawSchreierDatum.strong_get_mem_originalSubgroup _ hv ⟨j, hj⟩
  rwa [RawSchreierDatum.ofArrays_strong_get] at hm

theorem chain_word_mem
    (h : rawChainOK n (S.extract 0 k) S (base.map Fin.val).toArray W 4 = true)
    (w : List ℤ) (hw : lettersOK S.size w = true) :
    Rep n (wordA n S (rawInvs n S) w) (permOfArr n (wordA n S (rawInvs n S) w)) ∧
      permOfArr n (wordA n S (rawInvs n S) w) ∈
        (RawSchreierDatum.ofArrays n hn S k hk base hb W).originalSubgroup := by
  obtain ⟨g, hg, hrep⟩ := wordA_mem' (chain_strong_spec h) w hw
  rw [permOfArr_eq_of_rep hrep]
  exact ⟨hrep, hg⟩

end Chains

theorem genArrs_size : genArrs.size = 10 := by simp [genArrs, rootPairs]

theorem omegaS_size : omegaS.size = 17 := by
  rw [omegaS, size_pushWords]
  simp [genArrs_size, omegaWords]

theorem autS_size : autS.size = 18 := by
  rw [autS, size_pushWords, genArrs_size]
  simp [autWords]

theorem omega1S_size : omega1S.size = 17 := by
  rw [omega1S, size_pushWords]
  simp [genArrs_size, omegaWords]

theorem sylowGens_size : sylowGens.size = 5 := by simp [sylowGens, sylowIdx]

theorem sylowS_size : sylowS.size = 8 := by
  rw [sylowS, size_pushWords, sylowGens_size]
  simp [sylowWords]

@[expose] def omegaQ : RawSchreierDatum 360 :=
  RawSchreierDatum.ofArrays 360 (by norm_num) omegaS 8 (by rw [omegaS_size]; norm_num) omegaBase
    (by decide) (wordsOf 8 omegaWords)

@[expose] def autQ : RawSchreierDatum 360 :=
  RawSchreierDatum.ofArrays 360 (by norm_num) autS 10 (by rw [autS_size]; norm_num) autBase
    (by decide) (wordsOf 10 autWords)

@[expose] def omega1Q : RawSchreierDatum 120 :=
  RawSchreierDatum.ofArrays 120 (by norm_num) omega1S 8 (by rw [omega1S_size]; norm_num)
    omega1Base (by decide) (wordsOf 8 omegaWords)

@[expose] def sylowQ : RawSchreierDatum 360 :=
  RawSchreierDatum.ofArrays 360 (by norm_num) sylowS 5 (by rw [sylowS_size]; norm_num) sylowBase
    (by decide) (wordsOf 5 sylowWords)

@[expose] def omegaT : Subgroup (Equiv.Perm (Fin 360)) := omegaQ.originalSubgroup

@[expose] def autT : Subgroup (Equiv.Perm (Fin 360)) := autQ.originalSubgroup

@[expose] def omega1T : Subgroup (Equiv.Perm (Fin 120)) := omega1Q.originalSubgroup

@[expose] def sylowT : Subgroup (Equiv.Perm (Fin 360)) := sylowQ.originalSubgroup

@[expose] def gen (i : ℕ) : Equiv.Perm (Fin 360) := permOfArr 360 genArrs[i]!

theorem extract_getElem! {S : Array (Array ℕ)} {k i : ℕ} (hi : i < k) (hk : k ≤ S.size) :
    (S.extract 0 k)[i]! = S[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos S i (by omega), Array.getElem_extract]
  simp

theorem omegaS_getElem! {i : ℕ} (hi : i < 8) : omegaS[i]! = genArrs[i]! := by
  rw [omegaS, pushWords_getElem! _ _ (by simp [genArrs_size]; omega),
    extract_getElem! hi (by rw [genArrs_size]; norm_num)]

theorem autS_getElem! {i : ℕ} (hi : i < 10) : autS[i]! = genArrs[i]! := by
  rw [autS, pushWords_getElem! _ _ (by rw [genArrs_size]; omega)]

theorem map_getElem! {S : Array (Array ℕ)} {f : Array ℕ → Array ℕ} {i : ℕ} (hi : i < S.size) :
    (S.map f)[i]! = f S[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos S i hi]

theorem omega1S_getElem! {i : ℕ} (hi : i < 8) : omega1S[i]! = copy0Arr genArrs[i]! := by
  rw [omega1S, pushWords_getElem! _ _ (by simp [genArrs_size]; omega),
    map_getElem! (by simp [genArrs_size]; omega),
    extract_getElem! hi (by rw [genArrs_size]; norm_num)]

theorem sylowGens_getElem! {i : ℕ} (hi : i < 5) : sylowGens[i]! = genArrs[sylowIdx.getD i 0]! := by
  rw [sylowGens, getElem!_pos _ i (by simpa [sylowIdx] using hi), Array.getElem_map]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < sylowIdx.length by
    simpa [sylowIdx] using hi)]

theorem sylowS_getElem! {i : ℕ} (hi : i < 5) : sylowS[i]! = genArrs[sylowIdx.getD i 0]! := by
  rw [sylowS, pushWords_getElem! _ _ (by rw [sylowGens_size]; omega), sylowGens_getElem! hi]

theorem omegaT_eq : omegaT = Subgroup.closure {g | ∃ i < 8, gen i = g} := by
  rw [omegaT, omegaQ, ofArrays_originalSubgroup]
  refine congrArg Subgroup.closure (Set.ext fun g => ?_)
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [gen, omegaS_getElem! hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [gen, omegaS_getElem! hi]⟩

theorem autT_eq : autT = Subgroup.closure {g | ∃ i < 10, gen i = g} := by
  rw [autT, autQ, ofArrays_originalSubgroup]
  refine congrArg Subgroup.closure (Set.ext fun g => ?_)
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [gen, autS_getElem! hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [gen, autS_getElem! hi]⟩

theorem sylowT_eq : sylowT = Subgroup.closure {g | ∃ i < 5, gen (sylowIdx.getD i 0) = g} := by
  rw [sylowT, sylowQ, ofArrays_originalSubgroup]
  refine congrArg Subgroup.closure (Set.ext fun g => ?_)
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [gen, sylowS_getElem! hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [gen, sylowS_getElem! hi]⟩

theorem gen_mem_omegaT {i : ℕ} (hi : i < 8) : gen i ∈ omegaT := by
  rw [omegaT_eq]
  exact Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem gen_mem_autT {i : ℕ} (hi : i < 10) : gen i ∈ autT := by
  rw [autT_eq]
  exact Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem omegaT_le_autT : omegaT ≤ autT := by
  rw [omegaT_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact gen_mem_autT (by omega)

theorem sylowT_le_autT : sylowT ≤ autT := by
  rw [sylowT_eq, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  apply gen_mem_autT
  interval_cases i <;> decide

theorem rep_conjArr {t u : Array ℕ} {g h : Equiv.Perm (Fin 360)} (ht : Rep 360 t g)
    (hti : Rep 360 (invCand 360 t) g⁻¹) (hu : Rep 360 u h) :
    Rep 360 (conjArr t u) (g * h * g⁻¹) :=
  rep_compA (rep_compA ht hu) hti

theorem rhoPerm_lt {i : ℕ} (hi : i < 8) : rhoPerm.getD i 0 < 8 := by
  interval_cases i <;> decide

theorem tauPerm_lt {i : ℕ} (hi : i < 8) : tauPerm.getD i 0 < 8 := by
  interval_cases i <;> decide

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] [Finite G] {H : Subgroup G} {a : G}
    (h : ∀ g ∈ H, a * g * a⁻¹ ∈ H) : a ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj a).toMonoidHom ≤ H := by
    rintro _ ⟨g, hg, rfl⟩
    exact h g hg
  have heq : H.map (MulAut.conj a).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj a).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact h g
  · intro hg
    rw [← heq] at hg
    obtain ⟨g', hg', hgg'⟩ := hg
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgg'
    have : g' = g := mul_left_cancel (mul_right_cancel hgg')
    rwa [← this]

@[expose] def stab0 : Subgroup (Equiv.Perm (Fin 360)) where
  carrier := {g | ∀ p : Fin 360, (p : ℕ) < 120 ↔ ((g p : Fin 360) : ℕ) < 120}
  mul_mem' := fun {g h} hg hh p => (hh p).trans (hg (h p))
  one_mem' := fun _ => Iff.rfl
  inv_mem' := fun {g} hg p => by
    have := hg (g⁻¹ p)
    rw [show g (g⁻¹ p) = p by simp] at this
    exact this.symm

@[expose] def res0Fun (g : stab0) (j : Fin 120) : Fin 120 :=
  ⟨((g : Equiv.Perm (Fin 360)) ⟨j, by omega⟩ : ℕ), (g.2 ⟨j, by omega⟩).1 j.2⟩

theorem res0Fun_val (g : stab0) (j : Fin 120) :
    ((res0Fun g j : Fin 120) : ℕ) = ((g : Equiv.Perm (Fin 360)) ⟨j, by omega⟩ : ℕ) := rfl

theorem res0Fun_inv (g : stab0) (j : Fin 120) : res0Fun g⁻¹ (res0Fun g j) = j := by
  apply Fin.ext
  have e : (⟨(res0Fun g j : ℕ), by omega⟩ : Fin 360) = (g : Equiv.Perm (Fin 360)) ⟨j, by omega⟩ :=
    Fin.ext rfl
  change (((g⁻¹ : stab0) : Equiv.Perm (Fin 360)) ⟨(res0Fun g j : ℕ), _⟩ : ℕ) = j
  rw [e]
  simp

theorem res0Fun_inv' (g : stab0) (j : Fin 120) : res0Fun g (res0Fun g⁻¹ j) = j := by
  apply Fin.ext
  have e : (⟨(res0Fun g⁻¹ j : ℕ), by omega⟩ : Fin 360) =
      ((g⁻¹ : stab0) : Equiv.Perm (Fin 360)) ⟨j, by omega⟩ := Fin.ext rfl
  change ((g : Equiv.Perm (Fin 360)) ⟨(res0Fun g⁻¹ j : ℕ), _⟩ : ℕ) = j
  rw [e]
  simp

@[expose] def res0 : stab0 →* Equiv.Perm (Fin 120) where
  toFun g := ⟨res0Fun g, res0Fun g⁻¹, res0Fun_inv g, res0Fun_inv' g⟩
  map_one' := by
    ext j
    simp [res0Fun]
  map_mul' g h := by
    ext j
    simp [res0Fun]

theorem res0_apply_val (g : stab0) (j : Fin 120) :
    ((res0 g j : Fin 120) : ℕ) = ((g : Equiv.Perm (Fin 360)) ⟨j, by omega⟩ : ℕ) := rfl

@[expose] def gen1 (i : ℕ) : Equiv.Perm (Fin 120) := permOfArr 120 (copy0Arr genArrs[i]!)

theorem omega1T_eq : omega1T = Subgroup.closure {g | ∃ i < 8, gen1 i = g} := by
  rw [omega1T, omega1Q, ofArrays_originalSubgroup]
  refine congrArg Subgroup.closure (Set.ext fun g => ?_)
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [gen1, omega1S_getElem! hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [gen1, omega1S_getElem! hi]⟩

theorem copy0Arr_getElem! (t : Array ℕ) {j : ℕ} (hj : j < 120) : (copy0Arr t)[j]! = t[j]! := by
  rw [copy0Arr, getElem!_ofFn_nat _ hj]

@[expose] def sgen (j : ℕ) : Equiv.Perm (Fin 360) := permOfArr 360 omegaS[j]!

end CFSG.EvenSmallLie.OmegaEight
