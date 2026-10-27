module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowFour
public import CFSG.Sporadic.Co1Block.CentQ
public import CFSG.Sporadic.Co1Block.Co1Equiv

public section

namespace CFSG.EvenSporadicStandard.TwoCo1.HypOne

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1Block
  CFSG.ComponentClassification.M12Cover

theorem validRows_of_gtOK {G : Array (Array ℕ)} {T : GTree} (h : gtOK G T = true) :
    ∀ i < T.pts.size, validRows T.pts[i]! = true := by
  unfold gtOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hall⟩, -⟩, -⟩ := h
  intro i hi
  have hp := CFSG.Sporadic.Th.allIn_eq_true.1 hall i (Nat.zero_le _) hi
  simp only [gtPointOK, Bool.and_eq_true] at hp
  exact hp.1

theorem fourRows_of {p : Native.Rows} {s : GL24} (hp : MRep p s) (hv : validRows p = true)
    (h4 : s ^ 4 = 1) (h2 : s ^ 2 ≠ 1) : fourRows p = true := by
  have hss : MRep (Native.mul p p) (s * s) := hp.mul hp
  have hss4 : MRep (Native.mul (Native.mul p p) (Native.mul p p)) (s * s * (s * s)) :=
    hss.mul hss
  have hv2 : validRows (Native.mul p p) = true :=
    CFSG.Sporadic.Co1.Module.TwoB.validRows_mulRows hv hv
  have hv4 : validRows (Native.mul (Native.mul p p) (Native.mul p p)) = true :=
    CFSG.Sporadic.Co1.Module.TwoB.validRows_mulRows hv2 hv2
  have e4 : s * s * (s * s) = 1 := by
    have : s ^ 4 = s * s * (s * s) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    rw [← this]
    exact h4
  have h4' : MRep (Native.mul (Native.mul p p) (Native.mul p p)) 1 := e4 ▸ hss4
  have hrows : Native.mul (Native.mul p p) (Native.mul p p) = Native.one :=
    CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid hv4 validRows_one
      (h4'.trans MRep.one.symm)
  unfold fourRows
  rw [Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
  refine ⟨hrows, fun hone => h2 ?_⟩
  have h1 : MRep (Native.mul p p) 1 := hone ▸ MRep.one
  rw [pow_two]
  exact hss.eq h1

theorem five_le_card_conj {K : Subgroup GL24} (x : K) (g : ℕ → K) (v : ℕ → GL24)
    (hg : ∀ k < 5, ((g k * x * (g k)⁻¹ : K) : GL24) = v k)
    (hinj : ∀ i < 5, ∀ j < 5, v i = v j → i = j) : 5 ≤ Nat.card {y : K // IsConj x y} := by
  let φ : Fin 5 → {y : K // IsConj x y} := fun k =>
      ⟨g k * x * (g k)⁻¹, isConj_iff.2 ⟨g k, rfl⟩⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : v a = v b := by
      rw [← hg a a.2, ← hg b b.2]
      have := congrArg (fun y : {y : K // IsConj x y} => ((y : K) : GL24)) hab
      exact this
    exact Fin.ext (hinj a a.2 b b.2 h1)
  have := Nat.card_le_card_of_injective φ hφ
  simpa using this

theorem fourClassesLarge_of_trees {K : Subgroup GL24} {sg cg : Array Native.Rows} {T : GTree}
    {sgG kk : ℕ → GL24}
    (hsgrep : ∀ l < sg.size, valHom (sgG l) = rowsMatrix 24 sg[l]!) (hsgK : ∀ l, sgG l ∈ K)
    (hT : gtOK sg T = true) (hord : T.pts.size = 2 ^ (Nat.card K).factorization 2)
    (hk : ∀ l < cg.size, valHom (kk l) = rowsMatrix 24 cg[l]!) (hkK : ∀ l, kk l ∈ K)
    (hki : ∀ l < cg.size, mulRows 24 cg[l]! (cg.map Native.inv)[l]! = idRows 24)
    (hall : ∀ i < T.pts.size, fourRows T.pts[i]! = true →
      Native.conjAtLeast cg (cg.map Native.inv) T.pts[i]! 5 = true) : FourClassesLarge K := by
  obtain ⟨f, hf, -, hcl⟩ := prodTree_closure_eq valHom valHom_injective hT sgG hsgrep
  have hScard := prodTree_card valHom valHom_injective hT sgG hsgrep
  have hSK : Subgroup.closure (sgG '' {l | l < sg.size}) ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, -, rfl⟩
    exact hsgK l
  have hSord : Nat.card (Subgroup.closure (sgG '' {l | l < sg.size})) =
      2 ^ (Nat.card K).factorization 2 := by rw [hScard, hord]
  have hvalid := validRows_of_gtOK hT
  intro x hx4 hx2
  have hxg4 : (x : GL24) ^ 4 = 1 := by
    rw [← Subgroup.coe_pow, hx4, Subgroup.coe_one]
  have hxg2 : (x : GL24) ^ 2 ≠ 1 := fun h => hx2 (Subtype.ext (by
    rw [Subgroup.coe_pow, h, Subgroup.coe_one]))
  obtain ⟨c, hcK, hcS⟩ := HypOne.exists_conj_mem_of_card_pow_four hSK hSord x.2 hxg4
  have hconj : c⁻¹ * (x : GL24) * c = (MulAut.conj c⁻¹) (x : GL24) := by simp
  have hs4 : (c⁻¹ * (x : GL24) * c) ^ 4 = 1 := by
    rw [hconj, ← map_pow, hxg4, map_one]
  have hs2 : (c⁻¹ * (x : GL24) * c) ^ 2 ≠ 1 := by
    intro h2
    rw [hconj, ← map_pow] at h2
    exact hxg2 ((MulAut.conj c⁻¹).injective (by rw [h2, map_one]))
  have hcS' : c⁻¹ * (x : GL24) * c ∈
      (Subgroup.closure (sgG '' {l | l < sg.size}) : Set GL24) := hcS
  rw [hcl] at hcS'
  obtain ⟨i, hi, hsi⟩ := hcS'
  have hi' : i < T.pts.size := hi
  have hp : MRep T.pts[i]! (c⁻¹ * (x : GL24) * c) := by
    unfold MRep
    rw [← hsi]
    exact (hf i hi').symm
  have hfour : fourRows T.pts[i]! = true := fourRows_of hp (hvalid i hi') hs4 hs2
  have hcj := hall i hi' hfour
  simp only [Native.conjAtLeast, Bool.and_eq_true, decide_eq_true_eq] at hcj
  obtain ⟨hct, h5⟩ := hcj
  have hs' : valHom (c⁻¹ * (x : GL24) * c) = rowsMatrix 24 T.pts[i]! := hp.symm
  obtain ⟨f', hf', hinj'⟩ := conjTree_sound valHom hct kk hk hki (c⁻¹ * (x : GL24) * c) hs'
  have hz : ∀ k < 5, ∃ z : K, (((z * x * z⁻¹ : K) : GL24)) = f' k := by
    intro k hk5
    obtain ⟨⟨y, hy, hye⟩, -⟩ := hf' k (by omega)
    have hyK : y ∈ K := by
      have hle : Subgroup.closure (kk '' {l | l < cg.size}) ≤ K := by
        rw [Subgroup.closure_le]
        rintro _ ⟨l, -, rfl⟩
        exact hkK l
      exact hle hy
    refine ⟨⟨y * c⁻¹, K.mul_mem hyK (K.inv_mem hcK)⟩, ?_⟩
    rw [hye]
    show y * c⁻¹ * (x : GL24) * (y * c⁻¹)⁻¹ = y * (c⁻¹ * (x : GL24) * c) * y⁻¹
    group
  choose! z hz using hz
  exact five_le_card_conj x z f' hz (fun i hi j hj h => hinj' i (by omega) j (by omega) h)

theorem fourClassesLarge_of_sylowCheck
    {tR : Native.Rows} {t : GL24} (ht : MRep tR t) (htG : t ∈ GA)
    {d₁ : List (List ℤ)} {bidx : List ℕ} {d₂ : List (List ℤ)} {sIdx : List ℕ} {ord : ℕ}
    {K : Subgroup GL24} (hK : K = GA ⊓ Subgroup.centralizer {t})
    (hord : ord = 2 ^ (Nat.card K).factorization 2)
    (h : sylowCheckOf tR d₁ bidx d₂ sIdx ord = true) : FourClassesLarge K := by
  simp only [sylowCheckOf, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hD1, hD2⟩, hBall⟩, hT⟩, hsize⟩, hall⟩ := h
  have hrepB := rep_brayElts (bidx := bidx) ht hD1
  have hBGK : ∀ g ∈ brayEltsG t d₁ bidx, g ∈ K := by
    intro g hg
    rw [hK]
    refine Subgroup.mem_inf.2 ⟨brayElts_mem_GA htG g hg, ?_⟩
    obtain ⟨r, hr, hrg⟩ := forall₂_mem_left hrepB hg
    have e := (hBall r hr).1
    have h1 : MRep (Native.mul r tR) (g * t) := hrg.mul ht
    have h2 : MRep (Native.mul tR r) (t * g) := ht.mul hrg
    rw [e] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h2.eq h1).symm
  have hrepD2 := dag_rep hrepB d₂ hD2
  have hD2K : ∀ g ∈ dagG (brayEltsG t d₁ bidx) d₂, g ∈ K := dagG_mem hBGK d₂
  refine fourClassesLarge_of_trees
    (cg := (Native.brayElts (Native.brayRows tR d₁) bidx).toArray)
    (sgG := fun l => (dagG (brayEltsG t d₁ bidx) d₂).getD (sIdx.getD l 0) 1)
    (kk := fun l => (brayEltsG t d₁ bidx).getD l 1) ?_ (fun l => getD_mem_of_forall hD2K _) hT
    (hsize.trans hord) ?_ (fun l => getD_mem_of_forall hBGK l) ?_ ?_
  · intro l hl
    have hl' : l < sIdx.length := by simpa using hl
    rw [getElem!_toArray_map _ _ hl', List.getD_eq_getElem _ _ hl']
    exact (getD_rep hrepD2 MRep.one sIdx[l]).symm
  · intro l hl
    have hl' : l < (Native.brayElts (Native.brayRows tR d₁) bidx).length := by simpa using hl
    rw [getElem!_pos _ l hl, List.getElem_toArray, ← List.getD_eq_getElem _ _ hl']
    exact (getD_rep hrepB MRep.one l).symm
  · intro l hl
    have hmem : (Native.brayElts (Native.brayRows tR d₁) bidx).toArray[l]! ∈
        Native.brayElts (Native.brayRows tR d₁) bidx := by
      rw [getElem!_pos _ l hl, List.getElem_toArray]
      exact List.getElem_mem _
    rw [getElem!_pos (Array.map Native.inv _) l (by simpa using hl), Array.getElem_map,
      ← getElem!_pos _ l hl]
    exact (hBall _ hmem).2
  · intro i hi hfour
    rw [getElem!_pos _ i hi] at hfour ⊢
    have h := hall i hi
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [hfour] at h
      exact absurd h (by decide)
    · exact h

end CFSG.EvenSporadicStandard.TwoCo1.HypOne
