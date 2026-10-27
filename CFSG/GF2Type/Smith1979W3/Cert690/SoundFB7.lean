module

public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB7a
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB3
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB5

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 Module

abbrev cList (D : PGLData) (u : ℕ) : Array ℕ :=
  D.elems.filter fun k => Code.mul k u == Code.mul u k

abbrev stabList (D : PGLData) (e : ℕ) : Array ℕ :=
  D.elems.filter fun k => Code.act k e == e
abbrev cN (D : PGLData) (u : ℕ) : ℕ := (cList D u).size

abbrev cIdx (D : PGLData) (u : ℕ) : Std.HashMap ℕ ℕ := idxMapOf (cList D u)

abbrev cM (D : PGLData) (u : ℕ) : Array (Array ℕ) := mulIdxTable (cList D u) (cIdx D u)

abbrev cInvC (D : PGLData) (u : ℕ) : Array ℕ := invArr (cList D u)

abbrev cConjC (D : PGLData) (u : ℕ) : Array (Array ℕ) :=
  conjIdxTable (cList D u) (cList D u) (cInvC D u) (cIdx D u)

abbrev cOneIdx (D : PGLData) (u : ℕ) : ℕ := (cIdx D u).getD Code.one (cN D u)

abbrev cUIdx (D : PGLData) (u : ℕ) : ℕ := (cIdx D u).getD u (cN D u)

abbrev cPow2 (D : PGLData) (u : ℕ) : Array Bool := (cList D u).map fun a => pow2K a
def fEs : List ℕ :=
  (List.range 64).filter fun e =>
    e != 0 && !(qB false e) && !(vPlusVecs.contains e) && !(vStarVecs.contains e)

abbrev fList (D : PGLData) (e : ℕ) : Array ℕ := stabList D e

abbrev fN (D : PGLData) (e : ℕ) : ℕ := (fList D e).size

abbrev fIdx (D : PGLData) (e : ℕ) : Std.HashMap ℕ ℕ := idxMapOf (fList D e)

abbrev fM (D : PGLData) (e : ℕ) : Array (Array ℕ) := mulIdxTable (fList D e) (fIdx D e)

abbrev fIsInv (D : PGLData) (e : ℕ) : Array Bool :=
  (fList D e).map fun a => Code.mul a a == Code.one

abbrev fOneIdx (D : PGLData) (e : ℕ) : ℕ := (fIdx D e).getD Code.one (fN D e)

abbrev fConj (D : PGLData) (e : ℕ) : Array (Array ℕ) :=
  conjIdxTable (fList D e) D.elems D.invs (fIdx D e)

abbrev fCent (D : PGLData) (e : ℕ) : Array ℕ := centralMaskTable (fList D e) D.elems

abbrev fBadCent (D : PGLData) (e : ℕ) : Array ℕ :=
  (List.range D.elems.size).foldl
    (fun acc i => if pow2K (D.elems[i]!) then acc else acc.push ((fCent D e)[i]!)) #[]

theorem commute_of_code_mul_eq {D : PGLData} (hK : EnumCert kPGLGens D.elems.toList)
    {x y : V₀ ≃ₗ[ZMod 2] V₀} (hx : x ∈ KPGL) (hy : y ∈ KPGL)
    (hc : Code.mul (hK.code x) (hK.code y) = Code.mul (hK.code y) (hK.code x)) :
    x * y = y * x := by
  apply hK.eq_of_code_eq (Subgroup.mul_mem KPGL hx hy) (Subgroup.mul_mem KPGL hy hx)
  rw [hK.code_mul hx hy, hK.code_mul hy hx, hc]

theorem code_mul_comm_of_commute {D : PGLData} (hK : EnumCert kPGLGens D.elems.toList)
    {x y : V₀ ≃ₗ[ZMod 2] V₀} (hx : x ∈ KPGL) (hy : y ∈ KPGL)
    (hc : x * y = y * x) :
    Code.mul (hK.code x) (hK.code y) = Code.mul (hK.code y) (hK.code x) := by
  rw [← hK.code_mul hx hy, ← hK.code_mul hy hx, hc]

theorem natCard_centralizer_eq_filter (D : PGLData)
    (hK : EnumCert kPGLGens D.elems.toList) {u : V₀ ≃ₗ[ZMod 2] V₀} (huK : u ∈ KPGL) :
    Nat.card ↥(KPGL ⊓ Subgroup.centralizer ({u} : Set (V₀ ≃ₗ[ZMod 2] V₀))) =
      (cList D (hK.code u)).size := by
  let P : ℕ → Bool := fun k => Code.mul k (hK.code u) == Code.mul (hK.code u) k
  let e : {g : KPGL // P (hK.code g) = true} ≃
      ↥(KPGL ⊓ Subgroup.centralizer ({u} : Set (V₀ ≃ₗ[ZMod 2] V₀))) :=
    { toFun := fun g => ⟨g.1, by
        refine ⟨g.1.2, ?_⟩
        change (g.1 : V₀ ≃ₗ[ZMod 2] V₀) ∈ Subgroup.centralizer ({u} : Set (V₀ ≃ₗ[ZMod 2] V₀))
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply commute_of_code_mul_eq hK g.1.2 huK
        simpa [P, beq_iff_eq] using g.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
        have hcomm : x.1 * u = u * x.1 := Subgroup.mem_centralizer_singleton_iff.mp x.2.2
        have hc := code_mul_comm_of_commute hK x.2.1 huK hcomm
        simpa [P, beq_iff_eq] using hc⟩
      left_inv := fun g => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  calc Nat.card ↥(KPGL ⊓ Subgroup.centralizer ({u} : Set (V₀ ≃ₗ[ZMod 2] V₀)))
      = Nat.card {g : KPGL // P (hK.code g) = true} := (Nat.card_congr e).symm
    _ = (D.elems.toList.filter P).length := hK.natCard_filter P
    _ = (D.elems.filter P).size := by rw [← Array.length_toList, Array.toList_filter]
    _ = (cList D (hK.code u)).size := rfl

theorem pglF11Of_size_eq {D : PGLData} (h : pglF11Of D = true) {u : ℕ} (hu : u ∈ D.outers) :
    (cList D u).size = 12 := by
  unfold pglF11Of at h
  simp only [Bool.and_eq_true, Array.all_eq_true] at h
  obtain ⟨-, hAll⟩ := h
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hu
  have hi' := hAll i hi
  by_cases h12 : (cList D D.outers[i]).size = 12
  · exact h12
  · exfalso
    simp only [cList] at h12 hi'
    have hbeq :
        ((Array.filter (fun k => Code.mul k D.outers[i] == Code.mul D.outers[i] k) D.elems).size
          == 12) = false := by
      simpa [beq_iff_eq] using h12
    rw [hbeq] at hi'
    exact Bool.noConfusion hi'

theorem pglF11Of_facts {D : PGLData} (h0 : pglF11Of D = true) {u : ℕ} (hu : u ∈ D.outers) :
    cN D u = 12 ∧
    (hashSetOfArray (cList D u)).size = cN D u ∧
    cOneIdx D u < cN D u ∧
    (cList D u)[cOneIdx D u]! = Code.one ∧
    cUIdx D u < cN D u ∧
    (cList D u)[cUIdx D u]! = u ∧
    (cInvC D u).size = cN D u ∧
    (∀ i, i < cN D u → Code.mul (cList D u)[i]! (cInvC D u)[i]! = Code.one) ∧
    (∀ i, i < cN D u → ∀ j, j < cN D u →
      ((cM D u)[i]!)[j]! < cN D u ∧
      (cList D u)[((cM D u)[i]!)[j]!]! =
        Code.mul (cList D u)[i]! (cList D u)[j]!) ∧
    (∀ a, a < cN D u → ∀ b, b < cN D u →
      let y := ((cConjC D u)[a]!)[b]!
      let z := Code.mul (Code.mul (cList D u)[a]! (cList D u)[b]!) (cInvC D u)[a]!
      (y < cN D u ∧ (cList D u)[y]! = z) ∨
        (y = cN D u ∧ (cList D u).contains z = false)) ∧
    (∀ mask, mask < 2 ^ cN D u → mask.testBit (cOneIdx D u) = true →
      maskClosed (cM D u) mask (cN D u) = true →
      maskAllTrue (cPow2 D u) mask (cN D u) = true →
      (∀ c, c < cN D u →
        normalizesMask (cConjC D u)[c]! mask (cN D u) = true) →
      ∀ i, i < cN D u →
        (!mask.testBit i || i == cOneIdx D u || i == cUIdx D u) = true) := by
  have h := h0
  unfold pglF11Of at h
  simp only [Bool.and_eq_true, Array.all_eq_true] at h
  obtain ⟨-, hAll⟩ := h
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hu
  have hi' := hAll i hi
  have hn := pglF11Of_size_eq h0 (Array.mem_iff_getElem.mpr ⟨i, hi, rfl⟩)
  simp only [cList] at hn hi'
  rw [if_pos (by simpa [beq_iff_eq] using hn)] at hi'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    Array.all_eq_true] at hi'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, ⟨h6a, h6b⟩⟩, h7⟩, h8⟩, h9⟩ := hi'
  have h6b' : ∀ k, k < cN D D.outers[i] →
      Code.mul (cList D D.outers[i])[k]! (cInvC D D.outers[i])[k]! = Code.one :=
    fun k hk => h6b k (List.mem_range.mpr hk)
  have h7' : ∀ k, k < cN D D.outers[i] → ∀ l, l < cN D D.outers[i] →
      ((cM D D.outers[i])[k]!)[l]! < cN D D.outers[i] ∧
      (cList D D.outers[i])[((cM D D.outers[i])[k]!)[l]!]! =
        Code.mul (cList D D.outers[i])[k]! (cList D D.outers[i])[l]! :=
    fun k hk l hl => h7 k (List.mem_range.mpr hk) l (List.mem_range.mpr hl)
  have h8' : ∀ a, a < cN D D.outers[i] → ∀ b, b < cN D D.outers[i] →
      let y := ((cConjC D D.outers[i])[a]!)[b]!
      let z := Code.mul (Code.mul (cList D D.outers[i])[a]! (cList D D.outers[i])[b]!)
        (cInvC D D.outers[i])[a]!
      (y < cN D D.outers[i] ∧ (cList D D.outers[i])[y]! = z) ∨
        (y = cN D D.outers[i] ∧ (cList D D.outers[i]).contains z = false) := by
    intro a ha b hb
    have h := h8 a (List.mem_range.mpr ha) b (List.mem_range.mpr hb)
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.not_eq_true'] at h
    exact h
  have h9' : ∀ mask, mask < 2 ^ cN D D.outers[i] →
      mask.testBit (cOneIdx D D.outers[i]) = true →
      maskClosed (cM D D.outers[i]) mask (cN D D.outers[i]) = true →
      maskAllTrue (cPow2 D D.outers[i]) mask (cN D D.outers[i]) = true →
      (∀ c, c < cN D D.outers[i] →
        normalizesMask ((cConjC D D.outers[i])[c]!) mask (cN D D.outers[i]) = true) →
      ∀ k, k < cN D D.outers[i] →
        (!mask.testBit k || k == cOneIdx D D.outers[i] ||
          k == cUIdx D D.outers[i]) = true := by
    intro mask hm hbit hclosed hpow hnorm k hk
    have h := h9 mask (List.mem_range.mpr hm)
    have hguard :
        ((mask.testBit (cOneIdx D D.outers[i]) = true ∧
          maskClosed (cM D D.outers[i]) mask (cN D D.outers[i]) = true) ∧
          maskAllTrue (cPow2 D D.outers[i]) mask (cN D D.outers[i]) = true) ∧
          (∀ x ∈ List.range (cN D D.outers[i]),
            normalizesMask ((cConjC D D.outers[i])[x]!) mask
              (cN D D.outers[i]) = true) :=
      ⟨⟨⟨hbit, hclosed⟩, hpow⟩, fun x hx => hnorm x (List.mem_range.mp hx)⟩
    rw [if_pos hguard] at h
    exact (List.all_eq_true.mp h) k (List.mem_range.mpr hk)
  exact ⟨hn, h1, h2, h3, h4, h5, h6a, h6b', h7', h8', h9'⟩

theorem pglF11Of_outersOK {D : PGLData} (h : pglF11Of D = true) : pglOutersOK D = true := by
  unfold pglF11Of at h
  rw [Bool.and_eq_true] at h
  exact h.1

theorem pglF11_sound_of (hK : EnumCert kPGLGens (pglData ()).elems.toList)
    (hK0 : EnumCert kPGL0Gens (pglData ()).elems0.toList) (h : pglFactsCheck () = true) :
    ∀ u ∈ KPGL, u ∉ KPGL0 → u * u = 1 →
      Nat.card ↥(KPGL ⊓ Subgroup.centralizer {u}) = 12 ∧
      ∀ N : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), N ≤ KPGL ⊓ Subgroup.centralizer {u} →
        (∀ c ∈ KPGL ⊓ Subgroup.centralizer {u}, ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
        IsPGroup 2 N → N ≤ Subgroup.zpowers u := by
  intro u huK hu0 hu2
  classical
  let D := pglData ()
  have h11 : pglF11Of D = true := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -, -⟩ := pglFactsCheck_all h
    exact h11
  let uc := hK.code u
  have hucList : uc ∈ D.elems.toList := hK.code_mem huK
  have hucE : uc ∈ D.elems := Array.mem_toList_iff.mp hucList
  have huc0 : uc ∉ D.elems0 := by
    intro hm
    exact hu0 ((mem_KPGL0_iff_of_enum hK0 (hK.hasCode_code huK) (hK.lt uc hucList)).2 hm)
  have huc_ne : uc ≠ Code.one := by
    intro hc
    have hone : Code.HasCode ((1 : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) uc := by
      simpa [hc] using Code.hasCode_one
    have hu1 : u = 1 := Code.HasCode.eq_of_equiv (hK.hasCode_code huK) hone
    exact hu0 (hu1 ▸ Subgroup.one_mem KPGL0)
  have hisInv : isInvCode uc = true := by
    unfold isInvCode
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · simp [huc_ne]
    · have hcode : hK.code (u * u) = Code.mul uc uc := hK.code_mul huK huK
      rw [hu2, hK.code_one] at hcode
      exact beq_iff_eq.mpr hcode.symm
  have hucOut : uc ∈ D.outers :=
    (mem_outers_iff_of_ok (pglF11Of_outersOK h11)).mpr ⟨hucE, hisInv, huc0⟩
  obtain ⟨hn12, hnodup, hone_lt, hone_eq, huIdx_lt, huIdx_eq, hinv_size, hinv,
    hmexact, hcexact, hmask⟩ := pglF11Of_facts h11 hucOut
  have hcardCg : Nat.card ↥(KPGL ⊓ Subgroup.centralizer {u}) = 12 := by
    rw [natCard_centralizer_eq_filter D hK huK]
    exact hn12
  constructor
  · exact hcardCg
  · intro N hNle hNorm hP2
    haveI : Finite (V₀ ≃ₗ[ZMod 2] V₀) := finite_linearEquiv
    have hcardN_dvd : Nat.card N ∣ 12 := by
      have h := Subgroup.card_dvd_of_le hNle
      rwa [hcardCg] at h
    obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq (p := 2) hP2
    have hk2 : k ≤ 2 := by
      have h2k : 2 ^ k ∣ 12 := by rw [← hk]; exact hcardN_dvd
      by_contra h
      have h3 : 3 ≤ k := by omega
      have h8 : 2 ^ 3 ∣ 12 := (pow_dvd_pow 2 h3).trans h2k
      norm_num at h8
    have hpow16 : ∀ x ∈ N, x ^ 16 = 1 := by
      intro x hx
      have hord : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx
      rw [hk] at hord
      have hdvd4 : orderOf x ∣ 4 := hord.trans (pow_dvd_pow 2 hk2)
      have hdvd16 : orderOf x ∣ 16 := hdvd4.trans (by norm_num)
      exact (orderOf_dvd_iff_pow_eq_one).mp hdvd16
    let S : Finset ℕ := (Finset.range (cN D uc)).filter
      fun i => ∃ x : N, (cList D uc)[i]! = hK.code (x : V₀ ≃ₗ[ZMod 2] V₀)
    let m := maskOf S
    have hS_sub : S ⊆ Finset.range (cN D uc) := fun i hi => (Finset.mem_filter.mp hi).1
    have hm_lt : m < 2 ^ cN D uc := maskOf_lt hS_sub
    have index_of_mem : ∀ x ∈ N, ∃ q, q < cN D uc ∧
        (cList D uc)[q]! = hK.code x ∧ q ∈ S := by
      intro x hx
      have hxK : x ∈ KPGL := (hNle hx).1
      have hxComm : x * u = u * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (hNle hx).2
      have hxCodeList : hK.code x ∈ (cList D uc).toList := by
        rw [cList, Array.toList_filter]
        exact List.mem_filter.mpr ⟨hK.code_mem hxK, by
          rw [beq_iff_eq]
          simpa [uc] using code_mul_comm_of_commute hK hxK huK hxComm⟩
      have hxCodeC : hK.code x ∈ cList D uc := Array.mem_toList_iff.mp hxCodeList
      obtain ⟨hq_lt, hq_eq⟩ := idxMapOf_getD_mem hxCodeC
      refine ⟨(cIdx D uc).getD (hK.code x) (cN D uc), ?_, ?_, ?_⟩
      · simpa [cIdx, cN] using hq_lt
      · simpa [cIdx, cN] using hq_eq
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by simpa [cIdx, cN] using hq_lt),
            ⟨⟨x, hx⟩, by simpa [cIdx, cN] using hq_eq⟩⟩
    have hone_inS : cOneIdx D uc ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hone_lt,
        ⟨⟨1, Subgroup.one_mem N⟩, ?_⟩⟩
      exact hone_eq.trans hK.code_one.symm
    have hbit_one : m.testBit (cOneIdx D uc) = true := by
      rw [testBit_maskOf]
      simp [hone_inS]
    have hclosed : maskClosed (cM D uc) m (cN D uc) = true := by
      apply maskClosed_maskOf hS_sub
      intro i hi j hj
      obtain ⟨hiRange, ⟨x, hxEq⟩⟩ := Finset.mem_filter.mp hi
      obtain ⟨hjRange, ⟨y, hyEq⟩⟩ := Finset.mem_filter.mp hj
      have hi_lt : i < cN D uc := Finset.mem_range.mp hiRange
      have hj_lt : j < cN D uc := Finset.mem_range.mp hjRange
      obtain ⟨hMlt, hMeq⟩ := hmexact i hi_lt j hj_lt
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hMlt,
        ⟨⟨x * y, Subgroup.mul_mem N x.2 y.2⟩, ?_⟩⟩
      rw [hMeq, hxEq, hyEq]
      exact (hK.code_mul (hNle x.2).1 (hNle y.2).1).symm
    have hpow : maskAllTrue (cPow2 D uc) m (cN D uc) = true := by
      apply maskAllTrue_maskOf hS_sub
      intro i hi
      obtain ⟨hiRange, ⟨x, hxEq⟩⟩ := Finset.mem_filter.mp hi
      have hi_lt : i < (cList D uc).size := Finset.mem_range.mp hiRange
      have hxK : (x : V₀ ≃ₗ[ZMod 2] V₀) ∈ KPGL := (hNle x.2).1
      have hp : pow2K (hK.code (x : V₀ ≃ₗ[ZMod 2] V₀)) = true :=
        (EnumCert.pow2K_iff hK hxK).mpr (hpow16 x x.2)
      have hci : (cPow2 D uc)[i]! = pow2K ((cList D uc)[i]!) := by
        simp [cPow2, hi_lt]
      rw [hci, hxEq, hp]
    have hnorm : ∀ c, c < cN D uc →
        normalizesMask ((cConjC D uc)[c]!) m (cN D uc) = true := by
      intro c hc
      apply normalizesMask_maskOf
      intro i hi
      obtain ⟨hiRange, ⟨x, hxEq⟩⟩ := Finset.mem_filter.mp hi
      have hi_lt : i < cN D uc := Finset.mem_range.mp hiRange
      have hcList : (cList D uc)[c]! ∈ (cList D uc).toList := by
        rw [array_getElem!_eq_getElem_of_lt hc]
        exact Array.getElem_mem_toList hc
      have hcList' := hcList
      rw [cList, Array.toList_filter] at hcList'
      have hcInfo := List.mem_filter.mp hcList'
      have hcE : (cList D uc)[c]! ∈ D.elems.toList := hcInfo.1
      have hcCommCode : Code.mul ((cList D uc)[c]!) uc = Code.mul uc ((cList D uc)[c]!) :=
        beq_iff_eq.mp hcInfo.2
      let cg : V₀ ≃ₗ[ZMod 2] V₀ := hK.elem ((cList D uc)[c]!)
      have hcgK : cg ∈ KPGL := hK.elem_mem hcE
      have hcgCodeEq : hK.code cg = (cList D uc)[c]! := by
        simpa [cg] using hK.code_elem hcE
      have hcgComm : cg * u = u * cg := by
        apply commute_of_code_mul_eq hK hcgK huK
        rw [hcgCodeEq]
        exact hcCommCode
      have hcgCg : cg ∈ KPGL ⊓ Subgroup.centralizer {u} :=
        ⟨hcgK, Subgroup.mem_centralizer_singleton_iff.mpr hcgComm⟩
      have hzN : cg * x * cg⁻¹ ∈ N := hNorm cg hcgCg x x.2
      have hxK : (x : V₀ ≃ₗ[ZMod 2] V₀) ∈ KPGL := (hNle x.2).1
      have hiCList : (cList D uc)[i]! ∈ (cList D uc).toList := by
        rw [array_getElem!_eq_getElem_of_lt hi_lt]
        exact Array.getElem_mem_toList hi_lt
      have hiCList' := hiCList
      rw [cList, Array.toList_filter] at hiCList'
      have hiInfo := List.mem_filter.mp hiCList'
      have hiE : (cList D uc)[i]! ∈ D.elems.toList := hiInfo.1
      have hxElem : hK.elem ((cList D uc)[i]!) = x := by
        rw [hxEq]
        exact hK.elem_code hxK
      have hxCode : Code.HasCode ((x : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
          ((cList D uc)[i]!) := by
        simpa [hxElem] using hK.hasCode_elem hiE
      have hcgCode : Code.HasCode (cg : V₀ →ₗ[ZMod 2] V₀) ((cList D uc)[c]!) := by
        simpa [cg] using hK.hasCode_elem hcE
      have hinvCode : Code.HasCode ((cg⁻¹ : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
          ((cInvC D uc)[c]!) :=
        hasCode_inv_of_mul_eq_one hcgCode (hinv c hc)
      have hzCode : Code.HasCode (((cg * x * cg⁻¹ : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀))
          (Code.mul (Code.mul ((cList D uc)[c]!) ((cList D uc)[i]!))
            ((cInvC D uc)[c]!)) :=
        Code.HasCode.mul (Code.HasCode.mul hcgCode hxCode) hinvCode
      have hzK : cg * x * cg⁻¹ ∈ KPGL := (hNle hzN).1
      have hzComm : cg * x * cg⁻¹ ∈ Subgroup.centralizer {u} := (hNle hzN).2
      have hzCodeEq : hK.code (cg * x * cg⁻¹) =
          Code.mul (Code.mul ((cList D uc)[c]!) ((cList D uc)[i]!))
            ((cInvC D uc)[c]!) := by
        exact Code.HasCode.code_eq (hK.hasCode_code hzK) hzCode
          (hK.lt _ (hK.code_mem hzK)) (Code.mul_lt _ _)
      have hzCodeList : hK.code (cg * x * cg⁻¹) ∈ (cList D uc).toList := by
        rw [cList, Array.toList_filter]
        exact List.mem_filter.mpr ⟨hK.code_mem hzK, by
          have hzc : (cg * x * cg⁻¹) * u = u * (cg * x * cg⁻¹) :=
            Subgroup.mem_centralizer_singleton_iff.mp hzComm
          rw [beq_iff_eq]
          simpa [uc] using code_mul_comm_of_commute hK hzK huK hzc⟩
      have hzContains : (cList D uc).contains
          (Code.mul (Code.mul ((cList D uc)[c]!) ((cList D uc)[i]!))
            ((cInvC D uc)[c]!)) = true := by
        rw [← hzCodeEq]
        exact Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp hzCodeList)
      have hcex : let y := ((cConjC D uc)[c]!)[i]!
          let z := Code.mul (Code.mul ((cList D uc)[c]!) ((cList D uc)[i]!))
            ((cInvC D uc)[c]!)
          (y < cN D uc ∧ (cList D uc)[y]! = z) ∨
            (y = cN D uc ∧ (cList D uc).contains z = false) :=
        hcexact c hc i hi_lt
      dsimp only at hcex
      rcases hcex with ⟨hy_lt, hy_eq⟩ | ⟨hy_eq, hy_notmem⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hy_lt,
          ⟨⟨cg * x * cg⁻¹, hzN⟩, ?_⟩⟩
        rw [hy_eq, hzCodeEq]
      · exact absurd hzContains (by rw [hy_notmem]; exact Bool.noConfusion)
    have hfinal : ∀ x ∈ N, x ∈ Subgroup.zpowers u := by
      intro x hx
      obtain ⟨q, hq_lt, hq_eq, hq_inS⟩ := index_of_mem x hx
      have hbitq : m.testBit q = true := by
        rw [testBit_maskOf]
        simp [hq_inS]
      have hconcl := hmask m hm_lt hbit_one hclosed hpow hnorm q hq_lt
      have hq_case : q = cOneIdx D uc ∨ q = cUIdx D uc := by
        have hb : (q == cOneIdx D uc || q == cUIdx D uc) = true := by
          simpa [hbitq] using hconcl
        simp only [Bool.or_eq_true, beq_iff_eq] at hb
        rcases hb with h | h
        · exact Or.inl h
        · exact Or.inr h
      rcases hq_case with hq1 | hq2
      · have hx1 : x = 1 := by
          apply hK.eq_of_code_eq (hNle hx).1 (Subgroup.one_mem KPGL)
          rw [← hq_eq, hq1, hone_eq, hK.code_one]
        rw [hx1]
        exact Subgroup.one_mem _
      · have hxu : x = u := by
          apply hK.eq_of_code_eq (hNle hx).1 huK
          rw [← hq_eq, hq2, huIdx_eq]
        rw [hxu]
        exact Subgroup.mem_zpowers u
    exact hfinal

theorem pglF10Of_size_eq {D : PGLData} (h : pglF10Of D = true) {e : ℕ} (he : e ∈ fEs) :
    (fList D e).size = 16 := by
  unfold pglF10Of at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have hi := h e he
  by_cases h16 : (fList D e).size = 16
  · exact h16
  · exfalso
    simp only [fList, stabList] at h16 hi
    have hbeq :
        ((Array.filter (fun k => Code.act k e == e) D.elems).size == 16) = false := by
      simpa [beq_iff_eq] using h16
    rw [hbeq] at hi
    exact Bool.noConfusion hi

theorem pglF10Of_facts {D : PGLData} (h0 : pglF10Of D = true) {e : ℕ} (he : e ∈ fEs) :
    ((hashSetOfArray (fList D e)).size = fN D e ∧ fOneIdx D e < fN D e) ∧
    (fList D e)[fOneIdx D e]! = Code.one ∧
    (∀ i, i < fN D e → ∀ j, j < fN D e →
      ((fM D e)[i]!)[j]! < fN D e ∧
      (fList D e)[((fM D e)[i]!)[j]!]! =
        Code.mul (fList D e)[i]! (fList D e)[j]!) ∧
    (∀ hh, hh < D.elems.size → ∀ i, i < fN D e →
      let y := ((fConj D e)[hh]!)[i]!
      let z := Code.mul (Code.mul (D.elems[hh]!) (fList D e)[i]!) (D.invs[hh]!)
      (y < fN D e ∧ (fList D e)[y]! = z) ∨
        (y = fN D e ∧ (fList D e).contains z = false)) ∧
    (∀ mask, mask < 2 ^ fN D e → mask.testBit (fOneIdx D e) = true →
      4 ≤ bitCount (fN D e) mask →
      maskAllTrue (fIsInv D e) mask (fN D e) = true →
      maskClosed (fM D e) mask (fN D e) = true →
      (!((List.range D.elems.size).all fun hh =>
          normalizesMask ((fConj D e)[hh]!) mask (fN D e) ==
            (Code.act (D.elems[hh]!) e == e)) ||
        (fBadCent D e).any (fun m => (mask &&& m) == mask)) = true) := by
  have h := h0
  unfold pglF10Of at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have hi := h e he
  have h16 := pglF10Of_size_eq h0 he
  simp only [fList, stabList] at h16 hi
  rw [if_pos (by simpa [beq_iff_eq] using h16)] at hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hi
  obtain ⟨⟨⟨⟨⟨hset, hone_lt⟩, hone_eq⟩, hmexact⟩, hcexact⟩, hmask⟩ := hi
  refine ⟨⟨hset, hone_lt⟩, hone_eq, ?_, ?_, ?_⟩
  · intro i hi_lt j hj_lt
    exact hmexact i (List.mem_range.mpr hi_lt) j (List.mem_range.mpr hj_lt)
  · intro hh hhh i hi_lt
    have h := hcexact hh (List.mem_range.mpr hhh) i (List.mem_range.mpr hi_lt)
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.not_eq_true'] at h
    exact h
  · intro mask hm_lt hbit hfour hinv hclosed
    have h := hmask mask (List.mem_range.mpr hm_lt)
    have hguard : (mask.testBit (fOneIdx D e) = true ∧ 4 ≤ bitCount (fN D e) mask) ∧
        maskAllTrue (fIsInv D e) mask (fN D e) = true := ⟨⟨hbit, hfour⟩, hinv⟩
    rw [if_pos hguard] at h
    rw [if_pos hclosed] at h
    exact h

theorem fBadCent_any (D : PGLData) (e : ℕ) (p : ℕ → Bool) :
    (fBadCent D e).any p = true ↔
      ∃ i, i < D.elems.size ∧ pow2K (D.elems[i]!) = false ∧
        p ((fCent D e)[i]!) = true := by
  unfold fBadCent
  rw [foldl_push_any_ite]
  simp only [Array.any_empty, Bool.false_or]
  rw [List.any_eq_true]
  simp only [List.mem_range, Bool.and_eq_true, Bool.not_eq_true']

theorem pglF10_sound_of (hK : EnumCert kPGLGens (pglData ()).elems.toList)
    (hK0 : EnumCert kPGL0Gens (pglData ()).elems0.toList) (h : pglFactsCheck () = true) :
    ∀ e : V₀, e ≠ 0 → qModel false e = 0 → e ∉ VPlus → e ∉ VStar →
      ∀ L, ¬ CensusCond false KPGL L e := by
  intro e he0 hq0 hVP hVS L hCensus
  classical
  haveI : Finite (V₀ ≃ₗ[ZMod 2] V₀) := finite_linearEquiv
  let D := pglData ()
  obtain ⟨ec, hec_lt, hec_eq⟩ := exists_vec e
  have hec_ne : ec ≠ 0 := by
    intro h0
    apply he0
    rw [← hec_eq, h0, vec_zero]
  have hqB : qB false ec = false := by
    have h := hq0
    rw [← hec_eq, qModel_vec] at h
    cases hb : qB false ec
    · rfl
    · simp [hb] at h
  have hVP' : ec ∉ vPlusVecs := by
    intro hmem
    apply hVP
    rw [← hec_eq]
    exact mem_VPlus_iff.mpr ⟨ec, hmem, rfl⟩
  have hVS' : ec ∉ vStarVecs := by
    intro hmem
    apply hVS
    rw [← hec_eq]
    exact mem_VStar_iff.mpr ⟨ec, hmem, rfl⟩
  have he_es : ec ∈ fEs := by
    rw [fEs, List.mem_filter]
    refine ⟨List.mem_range.mpr hec_lt, ?_⟩
    simp [hec_ne, hqB, hVP', hVS']
  obtain ⟨h1, -, h3, -, -, -, -, -, -, h10, -, -, -⟩ := pglFactsCheck_all h
  have hinvProd := (pglF1Of_facts h1).2.1
  have h336 : Nat.card KPGL = 336 := by
    have hc := hK.natCard
    have hsize := (pglF3Of_facts h3).1
    simpa [KPGL, Array.length_toList, hsize] using hc
  obtain ⟨⟨hset, hone_lt⟩, hone_eq, hmexact, hcexact, hmask⟩ :=
    pglF10Of_facts h10 he_es
  have h16 : fN D ec = 16 := pglF10Of_size_eq h10 he_es
  obtain ⟨hLK, hfix, hinvL, hcardL, hnormCond, hP2Cg⟩ := hCensus
  let S : Finset ℕ := (Finset.range (fN D ec)).filter
    fun i => ∃ x : L, (fList D ec)[i]! = hK.code (x : V₀ ≃ₗ[ZMod 2] V₀)
  let m := maskOf S
  have hS_sub : S ⊆ Finset.range (fN D ec) := fun i hi => (Finset.mem_filter.mp hi).1
  have hm_lt : m < 2 ^ fN D ec := maskOf_lt hS_sub
  have code_mem_fList : ∀ x : L, hK.code (x : V₀ ≃ₗ[ZMod 2] V₀) ∈ fList D ec := by
    intro x
    have hxList : hK.code (x : V₀ ≃ₗ[ZMod 2] V₀) ∈ (fList D ec).toList := by
      rw [fList, stabList, Array.toList_filter]
      exact List.mem_filter.mpr ⟨hK.code_mem (hLK x.2), by
        rw [beq_iff_eq]
        have hact_lt : Code.act (hK.code (x : V₀ ≃ₗ[ZMod 2] V₀)) ec < 64 :=
          Code.act_lt _ _
        have hvec : Code.vec (Code.act (hK.code (x : V₀ ≃ₗ[ZMod 2] V₀)) ec) = Code.vec ec := by
          rw [← apply_vec_of_hasCode (hK.hasCode_code (hLK x.2)) ec]
          simpa [hec_eq] using hfix x x.2
        exact vec_injective_of_lt hact_lt hec_lt hvec⟩
    exact Array.mem_toList_iff.mp hxList
  let idxOf : L → ℕ := fun x => (fIdx D ec).getD (hK.code (x : V₀ ≃ₗ[ZMod 2] V₀)) (fN D ec)
  have hidx_lt : ∀ x : L, idxOf x < fN D ec := by
    intro x
    obtain ⟨hlt, -⟩ := idxMapOf_getD_mem (A := fList D ec) (code_mem_fList x)
    simpa [idxOf, fIdx, fN] using hlt
  have hidx_eq : ∀ x : L, (fList D ec)[idxOf x]! = hK.code (x : V₀ ≃ₗ[ZMod 2] V₀) := by
    intro x
    obtain ⟨-, heq⟩ := idxMapOf_getD_mem (A := fList D ec) (code_mem_fList x)
    simpa [idxOf, fIdx, fN] using heq
  have hidx_mem : ∀ x : L, idxOf x ∈ S := by
    intro x
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hidx_lt x), ⟨x, hidx_eq x⟩⟩
  let f : L → S := fun x => ⟨idxOf x, hidx_mem x⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hxy' : idxOf x = idxOf y := congrArg Subtype.val hxy
    apply Subtype.ext
    apply hK.eq_of_code_eq (hLK x.2) (hLK y.2)
    rw [← hidx_eq x, ← hidx_eq y, hxy']
  have hcardS : Nat.card L ≤ S.card := by
    haveI : Fintype ↥L := Fintype.ofFinite _
    have hc := Fintype.card_le_of_injective f hf_inj
    rw [Nat.card_eq_fintype_card]
    simpa only [Fintype.card_coe] using hc
  have hone_inS : fOneIdx D ec ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hone_lt,
      ⟨⟨1, Subgroup.one_mem L⟩, ?_⟩⟩
    exact hone_eq.trans hK.code_one.symm
  have hbit_one : m.testBit (fOneIdx D ec) = true := by
    rw [testBit_maskOf]
    simp [hone_inS]
  have hfour : 4 ≤ bitCount (fN D ec) m := by
    rw [bitCount_maskOf hS_sub]
    exact le_trans hcardL hcardS
  have hinv_all : maskAllTrue (fIsInv D ec) m (fN D ec) = true := by
    apply maskAllTrue_maskOf hS_sub
    intro i hi
    obtain ⟨hiRange, ⟨x, hxEq⟩⟩ := Finset.mem_filter.mp hi
    have hi_lt : i < fN D ec := Finset.mem_range.mp hiRange
    have hxi : (x : V₀ ≃ₗ[ZMod 2] V₀) * x = 1 := hinvL x x.2
    have hp : Code.mul (hK.code (x : V₀ ≃ₗ[ZMod 2] V₀))
        (hK.code (x : V₀ ≃ₗ[ZMod 2] V₀)) = Code.one := by
      have hc := hK.code_mul (hLK x.2) (hLK x.2)
      rw [hxi, hK.code_one] at hc
      exact hc.symm
    have hci : (fIsInv D ec)[i]! =
        (Code.mul ((fList D ec)[i]!) ((fList D ec)[i]!) == Code.one) := by
      simp [fIsInv, hi_lt]
    rw [hci, hxEq]
    exact beq_iff_eq.mpr hp
  have hclosed : maskClosed (fM D ec) m (fN D ec) = true := by
    apply maskClosed_maskOf hS_sub
    intro i hi j hj
    obtain ⟨hiRange, ⟨x, hxEq⟩⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjRange, ⟨y, hyEq⟩⟩ := Finset.mem_filter.mp hj
    have hi_lt : i < fN D ec := Finset.mem_range.mp hiRange
    have hj_lt : j < fN D ec := Finset.mem_range.mp hjRange
    obtain ⟨hMlt, hMeq⟩ := hmexact i hi_lt j hj_lt
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hMlt,
      ⟨⟨x * y, Subgroup.mul_mem L x.2 y.2⟩, ?_⟩⟩
    rw [hMeq, hxEq, hyEq]
    exact (hK.code_mul (hLK x.2) (hLK y.2)).symm
  have hzg_code : ∀ hh, hh < D.elems.size → ∀ x : L,
      hK.code (hK.elem (D.elems[hh]!) * x * (hK.elem (D.elems[hh]!))⁻¹) =
        Code.mul (Code.mul (D.elems[hh]!) (hK.code (x : V₀ ≃ₗ[ZMod 2] V₀)))
          (D.invs[hh]!) := by
    intro hh hhh x
    have hhE : D.elems[hh]! ∈ D.elems.toList := by
      rw [array_getElem!_eq_getElem_of_lt hhh]
      exact Array.getElem_mem_toList hhh
    have hgK : hK.elem (D.elems[hh]!) ∈ KPGL := hK.elem_mem hhE
    have hxK : (x : V₀ ≃ₗ[ZMod 2] V₀) ∈ KPGL := hLK x.2
    have hzK : hK.elem (D.elems[hh]!) * x * (hK.elem (D.elems[hh]!))⁻¹ ∈ KPGL :=
      Subgroup.mul_mem KPGL
        (Subgroup.mul_mem KPGL hgK hxK) (Subgroup.inv_mem KPGL hgK)
    have hHas : Code.HasCode
        (((hK.elem (D.elems[hh]!) * x * (hK.elem (D.elems[hh]!))⁻¹ :
          V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀))
        (Code.mul (Code.mul (D.elems[hh]!) (hK.code (x : V₀ ≃ₗ[ZMod 2] V₀)))
          (D.invs[hh]!)) := by
      exact Code.HasCode.mul
        (Code.HasCode.mul (hK.hasCode_elem hhE) (hK.hasCode_code hxK))
        (hasCode_inv_of_mul_eq_one (hK.hasCode_elem hhE) (hinvProd hh hhh))
    exact Code.HasCode.code_eq (hK.hasCode_code hzK) hHas
      (hK.lt _ (hK.code_mem hzK)) (Code.mul_lt _ _)
  have normEq_forward : ∀ hh, hh < D.elems.size →
      normalizesMask ((fConj D ec)[hh]!) m (fN D ec) = true →
      hK.elem (D.elems[hh]!) ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
    intro hh hhh hnorm
    apply Subgroup.mem_normalizer_fintype
    intro x hxL
    have hhE : D.elems[hh]! ∈ D.elems.toList := by
      rw [array_getElem!_eq_getElem_of_lt hhh]
      exact Array.getElem_mem_toList hhh
    have hgK : hK.elem (D.elems[hh]!) ∈ KPGL := hK.elem_mem hhE
    have hxK : (x : V₀ ≃ₗ[ZMod 2] V₀) ∈ KPGL := hLK hxL
    have hxLmem : x ∈ L := hxL
    let i := idxOf ⟨x, hxLmem⟩
    have hi_lt : i < fN D ec := hidx_lt ⟨x, hxLmem⟩
    have hi_eq : (fList D ec)[i]! = hK.code (x : V₀ ≃ₗ[ZMod 2] V₀) := hidx_eq ⟨x, hxLmem⟩
    have hi_inS : i ∈ S := hidx_mem ⟨x, hxLmem⟩
    have hrow : (maskOf S).testBit (((fConj D ec)[hh]!)[i]!) = true := by
      have h := hnorm
      unfold normalizesMask at h
      rw [List.all_eq_true] at h
      have hi := h i (List.mem_range.mpr hi_lt)
      simp only [m, testBit_maskOf, hi_inS, decide_true, Bool.not_true, Bool.false_or] at hi
      simpa [testBit_maskOf] using hi
    have hy_inS : ((fConj D ec)[hh]!)[i]! ∈ S := by
      have hdec : decide (((fConj D ec)[hh]!)[i]! ∈ S) = true := by
        rw [← testBit_maskOf]
        exact hrow
      simpa using hdec
    have hy_lt : ((fConj D ec)[hh]!)[i]! < fN D ec :=
      Finset.mem_range.mp (hS_sub hy_inS)
    have hcex := hcexact hh hhh i hi_lt
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.not_eq_true'] at hcex
    obtain ⟨yEl, hyCodeEq⟩ := (Finset.mem_filter.mp hy_inS).2
    rcases hcex with ⟨-, hzEq⟩ | ⟨hy_eqn, -⟩
    · have hyz : hK.code (yEl : V₀ ≃ₗ[ZMod 2] V₀) =
          hK.code (hK.elem (D.elems[hh]!) * x * (hK.elem (D.elems[hh]!))⁻¹) := by
        rw [← hyCodeEq, hzEq, hzg_code hh hhh ⟨x, hxLmem⟩, hi_eq]
      have hyzEq : (yEl : V₀ ≃ₗ[ZMod 2] V₀) =
          hK.elem (D.elems[hh]!) * x * (hK.elem (D.elems[hh]!))⁻¹ := by
        apply hK.eq_of_code_eq (hLK yEl.2)
        · exact Subgroup.mul_mem KPGL
            (Subgroup.mul_mem KPGL hgK hxK) (Subgroup.inv_mem KPGL hgK)
        · exact hyz
      have hmem : (yEl : V₀ ≃ₗ[ZMod 2] V₀) ∈ L := yEl.2
      rwa [hyzEq] at hmem
    · exfalso
      rw [hy_eqn] at hy_lt
      exact Nat.lt_irrefl _ hy_lt
  have normEq_reverse : ∀ hh, hh < D.elems.size →
      hK.elem (D.elems[hh]!) ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) →
      normalizesMask ((fConj D ec)[hh]!) m (fN D ec) = true := by
    intro hh hhh hnormL
    apply normalizesMask_maskOf
    intro i hi
    obtain ⟨hiRange, ⟨x, hxEq⟩⟩ := Finset.mem_filter.mp hi
    have hi_lt : i < fN D ec := Finset.mem_range.mp hiRange
    have hhE : D.elems[hh]! ∈ D.elems.toList := by
      rw [array_getElem!_eq_getElem_of_lt hhh]
      exact Array.getElem_mem_toList hhh
    have hxK : (x : V₀ ≃ₗ[ZMod 2] V₀) ∈ KPGL := hLK x.2
    have hzgL : hK.elem (D.elems[hh]!) * x * (hK.elem (D.elems[hh]!))⁻¹ ∈ L := by
      have hiff := (Subgroup.mem_set_normalizer_iff.mp hnormL) (x : V₀ ≃ₗ[ZMod 2] V₀)
      exact hiff.mp x.2
    have hzK : hK.elem (D.elems[hh]!) * x * (hK.elem (D.elems[hh]!))⁻¹ ∈ KPGL :=
      hLK hzgL
    have hzCode := hzg_code hh hhh x
    have hzC : hK.code (hK.elem (D.elems[hh]!) * x * (hK.elem (D.elems[hh]!))⁻¹) ∈
        fList D ec := code_mem_fList ⟨_, hzgL⟩
    have hcex := hcexact hh hhh i hi_lt
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.not_eq_true'] at hcex
    rcases hcex with ⟨hy_lt, hy_eq⟩ | ⟨hy_eqn, hy_notmem⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hy_lt,
        ⟨⟨hK.elem (D.elems[hh]!) * x * (hK.elem (D.elems[hh]!))⁻¹, hzgL⟩, ?_⟩⟩
      rw [hy_eq, hxEq]
      exact hzCode.symm
    · exfalso
      have hcontains : (fList D ec).contains
          (Code.mul (Code.mul (D.elems[hh]!) (fList D ec)[i]!) (D.invs[hh]!)) = true := by
        rw [hxEq, ← hzCode]
        exact Array.contains_iff_mem.mpr hzC
      rw [hy_notmem] at hcontains
      exact Bool.noConfusion hcontains
  have normEq_iff : ∀ hh, hh < D.elems.size →
      (normalizesMask ((fConj D ec)[hh]!) m (fN D ec) = true ↔
        hK.elem (D.elems[hh]!) ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀))) :=
    fun hh hhh => ⟨normEq_forward hh hhh, normEq_reverse hh hhh⟩
  have hmaskRes := hmask m hm_lt hbit_one hfour hinv_all hclosed
  by_cases hbad : (fBadCent D ec).any (fun mm => (m &&& mm) == m) = true
  · obtain ⟨i, hi, hpow, hsub⟩ :=
      (fBadCent_any D ec (fun mm => (m &&& mm) == m)).mp hbad
    have hiE : D.elems[i]! ∈ D.elems.toList := by
      rw [array_getElem!_eq_getElem_of_lt hi]
      exact Array.getElem_mem_toList hi
    let gh : V₀ ≃ₗ[ZMod 2] V₀ := hK.elem (D.elems[i]!)
    have hgK : gh ∈ KPGL := hK.elem_mem hiE
    have hgCode : hK.code gh = D.elems[i]! := by
      simpa [gh] using hK.code_elem hiE
    have hgComm : gh ∈ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hxL
      let j := idxOf ⟨x, hxL⟩
      have hj_lt : j < fN D ec := hidx_lt ⟨x, hxL⟩
      have hj_eq : (fList D ec)[j]! = hK.code (x : V₀ ≃ₗ[ZMod 2] V₀) := hidx_eq ⟨x, hxL⟩
      have hj_inS : j ∈ S := hidx_mem ⟨x, hxL⟩
      have hbitj : m.testBit j = true := by
        rw [testBit_maskOf]
        simp [hj_inS]
      have hcentbit : ((fCent D ec)[i]!).testBit j = true := by
        have hand := congrArg (fun z => z.testBit j) (beq_iff_eq.mp hsub)
        rw [Nat.testBit_land, hbitj] at hand
        simpa using hand
      have hcm := (centralMaskTable_testBit (A := fList D ec) (K := D.elems) hi hj_lt).mp
        hcentbit
      have hcomm : (x : V₀ ≃ₗ[ZMod 2] V₀) * gh = gh * x := by
        apply commute_of_code_mul_eq hK (hLK hxL) hgK
        simpa [hgCode, hj_eq, gh] using (beq_iff_eq.mp hcm).symm
      exact hcomm
    have hgCg : gh ∈ KPGL ⊓ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) :=
      ⟨hgK, hgComm⟩
    obtain ⟨j, hjord⟩ := hP2Cg.exists_orderOf_eq_pow (⟨gh, hgCg⟩ : ↥(KPGL ⊓
      Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀))))
    have hjordG : orderOf gh = 2 ^ j := by
      have h := Subgroup.orderOf_coe (⟨gh, hgCg⟩ : ↥(KPGL ⊓
        Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀))))
      exact h.trans hjord
    have hdvd : 2 ^ j ∣ 336 := by
      rw [← hjordG, ← h336]
      exact Subgroup.orderOf_dvd_natCard KPGL hgK
    have hj4 : j ≤ 4 := by
      by_contra hj5
      have h5 : 5 ≤ j := by omega
      have h32 : 2 ^ 5 ∣ 336 := (pow_dvd_pow 2 h5).trans hdvd
      norm_num at h32
    have hdvd16 : orderOf gh ∣ 16 := by
      rw [hjordG]
      exact pow_dvd_pow 2 hj4
    have hgh16 : gh ^ 16 = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd16
    have hpowFalse : pow2K (hK.code gh) = false := by
      simpa [hgCode] using hpow
    exact (EnumCert.pow2K_eq_false_iff hK hgK).mp hpowFalse hgh16
  · have hnormEqFalse :
        ((List.range D.elems.size).all fun hh =>
          normalizesMask ((fConj D ec)[hh]!) m (fN D ec) ==
            (Code.act (D.elems[hh]!) ec == ec)) = false := by
      have h := hmaskRes
      have hbadFalse : (fBadCent D ec).any (fun mm => (m &&& mm) == m) = false :=
        Bool.eq_false_of_not_eq_true hbad
      rw [hbadFalse] at h
      simpa [Bool.not_eq_true'] using h
    obtain ⟨hh, hhh_mem, hneq⟩ := List.all_eq_false.mp hnormEqFalse
    have hneqEq : (normalizesMask ((fConj D ec)[hh]!) m (fN D ec) ==
        (Code.act (D.elems[hh]!) ec == ec)) = false :=
      Bool.eq_false_of_not_eq_true hneq
    have hhh : hh < D.elems.size := List.mem_range.mp hhh_mem
    have hhE : D.elems[hh]! ∈ D.elems.toList := by
      rw [array_getElem!_eq_getElem_of_lt hhh]
      exact Array.getElem_mem_toList hhh
    let g : V₀ ≃ₗ[ZMod 2] V₀ := hK.elem (D.elems[hh]!)
    have hgK : g ∈ KPGL := hK.elem_mem hhE
    have fixesEq : ((Code.act (D.elems[hh]!) ec == ec) = true) ↔ g e = e := by
      constructor
      · intro hfix
        have hact : Code.act (D.elems[hh]!) ec = ec := beq_iff_eq.mp hfix
        rw [← hec_eq, apply_vec_of_hasCode (hK.hasCode_elem hhE) ec, hact]
      · intro hfix
        have hvec : Code.vec (Code.act (D.elems[hh]!) ec) = Code.vec ec := by
          rw [← apply_vec_of_hasCode (hK.hasCode_elem hhE) ec]
          simpa [hec_eq] using hfix
        have hact : Code.act (D.elems[hh]!) ec = ec :=
          vec_injective_of_lt (Code.act_lt _ _) hec_lt hvec
        exact beq_iff_eq.mpr hact
    have hnormIff := normEq_iff hh hhh
    by_cases hnorm : normalizesMask ((fConj D ec)[hh]!) m (fN D ec) = true
    · have hgNorm : g ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) :=
        hnormIff.mp hnorm
      have hfixFalse : (Code.act (D.elems[hh]!) ec == ec) = false := by
        by_contra hf
        have hft : (Code.act (D.elems[hh]!) ec == ec) = true :=
          Bool.eq_true_of_not_eq_false hf
        rw [hnorm, hft] at hneqEq
        exact Bool.noConfusion hneqEq
      have hgFixNe : g e ≠ e := by
        intro hge
        have hft : (Code.act (D.elems[hh]!) ec == ec) = true := fixesEq.mpr hge
        rw [hfixFalse] at hft
        exact Bool.noConfusion hft
      exact hgFixNe ((hnormCond g hgK).mp hgNorm)
    · have hnormFalse : normalizesMask ((fConj D ec)[hh]!) m (fN D ec) = false := by
        simpa using hnorm
      have hfixTrue : (Code.act (D.elems[hh]!) ec == ec) = true := by
        by_contra hf
        have hff : (Code.act (D.elems[hh]!) ec == ec) = false :=
          Bool.eq_false_of_not_eq_true hf
        rw [hnormFalse, hff] at hneqEq
        exact Bool.noConfusion hneqEq
      have hgFix : g e = e := fixesEq.mp hfixTrue
      have hgNotNorm : g ∉ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
        intro hmem
        have htrue : normalizesMask ((fConj D ec)[hh]!) m (fN D ec) = true :=
          hnormIff.mpr hmem
        rw [hnormFalse] at htrue
        exact Bool.noConfusion htrue
      exact hgNotNorm ((hnormCond g hgK).mpr hgFix)

end CFSG.GF2Type.Smith1979W3.Cert690

end
