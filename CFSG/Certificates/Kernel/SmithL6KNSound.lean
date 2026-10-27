module

public import Certificates.Data.Kernel.SmithL6KN
public import CFSG.Certificates.Kernel.SmithL6KUSound

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6

theorem allFrom_sound {f : Nat → Bool} : ∀ {n a : Nat}, allFrom f a n = true →
    ∀ v, a ≤ v → v < a + n → f v = true := by
  intro n
  induction n with
  | zero => intro a _ v h1 h2; omega
  | succ n ih =>
    intro a h v h1 h2
    have h' : (f a && allFrom f (a + 1) n) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h'.1
    · exact ih h'.2 v hlt (by omega)

theorem keyTri_inj {x y : Nat} (h : keyTri x = keyTri y) : x = y := by
  unfold keyTri at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  omega

section Packed

variable {C I : Nat} (hC : ∀ k < 1953, fldW 12 C k = codeOf (tvPair k))
  (hI : ∀ n < 4096, fldW 11 I n = tvIdxTab[n]!)
include hC hI

theorem tvImgQ_eq {j a : Nat} (hj : j < 1953) (ha : a < 1953) : tvImgQ C I j a = tvImg j a := by
  unfold tvImgQ
  rw [conjF_eq]
  exact tvImgP_eq hC hI hj ha

theorem isPartnerK_eq {u : Nat} (hu : u < 1953) : isPartnerK C I u = isPartner u := by
  unfold isPartnerK isPartner
  rw [tvImgQ_eq hC hI (j := 0) (by decide) hu, tvImgQ_eq hC hI (a := 0) hu (by decide)]

theorem partReach {roots : List Nat} {recs : List (Nat × Nat × Nat)}
    (h : treeK 1953 1953 (partRootK C I) (partEdgeK C I) roots recs = true) :
    Reach 1953 1953 (fun v => v == 31 || !isPartner v)
      (fun g u v => tvImg g 0 == 0 && tvImg g u == v && (!isPartner v || isPartner u)) := by
  refine ((reach_of_treeK h).roots fun v hv hr => ?_).mono fun g hg u hu v hv he => ⟨g, hg, ?_⟩
  · unfold partRootK at hr
    rwa [isPartnerK_eq hC hI hv] at hr
  · unfold partEdgeK at he
    rwa [tvImgQ_eq hC hI (a := 0) hg (by decide), tvImgQ_eq hC hI hg hu, isPartnerK_eq hC hI hu,
      isPartnerK_eq hC hI hv] at he

theorem genOK_sound {M : Nat} (h : genOK C I M = true) {g : Nat} (hg : g < 1953)
    (hm : M.testBit g = true) : tvImg g 0 = 0 ∧ tvImg g 31 = 31 := by
  have e := allFrom_sound h g (Nat.zero_le _) (by omega)
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, beq_iff_eq] at e
  rcases e with e | ⟨e0, e31⟩
  · rw [hm] at e
    exact absurd e Bool.noConfusion
  · rw [tvImgQ_eq hC hI hg (by decide)] at e0 e31
    exact ⟨e0, e31⟩

theorem fourReach {key rec : Nat → Nat} {M root : Nat} (hgen : genOK C I M = true)
    (hrows : ∀ v < 20160, fourRowK C I key rec M root v = true)
    (hr : key root = fourKey fourBase) :
    ∀ v < 20160, Relation.ReflTransGen
      (fun s t => ∃ g < 1953, tvImg g 0 = 0 ∧ tvImg g 31 = 31 ∧ t = fourStep g s)
      fourBase (keyTri (key v)) := by
  suffices hkey : ∀ d v, rec v >>> 26 < d → v < 20160 → Relation.ReflTransGen
      (fun s t => ∃ g < 1953, tvImg g 0 = 0 ∧ tvImg g 31 = 31 ∧ t = fourStep g s)
      fourBase (keyTri (key v)) from fun v hv => hkey _ v (Nat.lt_succ_self _) hv
  intro d
  induction d with
  | zero => intro v hd; omega
  | succ d ih =>
    intro v hd hv
    have h := hrows v hv
    unfold fourRowK at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨h1, -⟩ := h
    rcases h1 with (h1 | h1) | h1
    · exact absurd hv h1
    · have e : keyTri (fourKey fourBase) = fourBase := by decide
      have e' : keyTri (key v) = fourBase := by rw [h1, hr, e]
      exact e' ▸ Relation.ReflTransGen.refl
    · obtain ⟨⟨⟨⟨hp, hdp⟩, hg⟩, hm⟩, he⟩ := h1
      generalize rec v % 32768 = p at hp hdp he
      generalize (rec v >>> 15) % 2048 = g at hg hm he
      have hQ := ih p (by omega) hp
      obtain ⟨h0, h31⟩ := genOK_sound hC hI hgen hg hm
      unfold fourEdgeK at he
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
      obtain ⟨⟨⟨hc, e1⟩, e2⟩, e3⟩ := he
      have ha : (keyTri (key p)).1 < 1953 := Nat.mod_lt _ (by decide)
      have hb : (keyTri (key p)).2.1 < 1953 := Nat.mod_lt _ (by decide)
      rw [tvImgQ_eq hC hI hg ha] at e1
      rw [tvImgQ_eq hC hI hg hb] at e2
      rw [tvImgQ_eq hC hI hg hc] at e3
      exact hQ.tail ⟨g, hg, h0, h31, Prod.ext e1 (Prod.ext e2 e3)⟩

theorem fourOrbit {key rec : Nat → Nat} {M root : Nat} (hgen : genOK C I M = true)
    (hch : ∀ k < 21, fourChunkK C I key rec M root k = true)
    (hr : key root = fourKey fourBase) :
    ∃ L : List (Nat × Nat × Nat), L.length = 20160 ∧ L.Nodup ∧ ∀ t ∈ L,
      Relation.ReflTransGen
        (fun s t => ∃ g < 1953, tvImg g 0 = 0 ∧ tvImg g 31 = 31 ∧ t = fourStep g s) fourBase t := by
  have hrows : ∀ v < 20160, fourRowK C I key rec M root v = true := fun v hv =>
    allFrom_sound (hch (v / 1000) (by omega)) v (by omega) (by omega)
  have hinc : ∀ i j, i < j → j < 20160 → key i < key j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have h := hrows j (by omega)
      unfold fourRowK at h
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq] at h
      have hs : key j < key (j + 1) := h.2.resolve_left (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h1 | h1
      · exact Nat.lt_trans (ih h1 (by omega)) hs
      · rw [h1]
        exact hs
  refine ⟨(List.range 20160).map fun v => keyTri (key v), by simp, ?_, ?_⟩
  · rw [List.Nodup, List.pairwise_map]
    refine List.pairwise_lt_range.imp_of_mem fun {x y} _ hy hxy e => ?_
    exact Nat.ne_of_lt (hinc x y hxy (List.mem_range.1 hy)) (keyTri_inj e)
  · intro t ht
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ht
    exact fourReach hC hI hgen hrows hr v (List.mem_range.1 hv)

end Packed

end CFSG.SmithL6.K
