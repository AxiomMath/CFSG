module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Codes
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabBuild

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open GenData CFSG.Quasithin.G2U

@[expose] def pcCodes (gens : List (List ℕ)) (G : GenData) : Array (List ℕ) :=
  G.walk onePc (fun c s => mulPc c (gens.getD s []))

@[expose] def pcTabCheck (gens : List (List ℕ)) (G : GenData) : Bool :=
  let es := pcCodes gens G
  G.ok && gens.length == G.ng && allCheck canonPc es && distinctCheck es &&
    (List.range G.n).all fun i => (List.range G.ng).all fun s =>
      es.getD (G.rtAt i s) [] == mulPc (es.getD i []) (gens.getD s [])

@[expose] def eltOf {Γ : Type*} [Group Γ] (G : GenData) (g : ℕ → Γ) (i : ℕ) : Γ :=
  (G.walk (1 : Γ) (fun a s => a * g s)).getD i 1

private theorem getD_eq_of_lt {α : Type*} {a : Array α} {i : ℕ} (h : i < a.size) (d : α) :
    a.getD i d = a[i]'h := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  rfl

private theorem getD_default_congr {α : Type*} {a : Array α} {i : ℕ} (h : i < a.size)
    (d e : α) : a.getD i d = a.getD i e :=
  (getD_eq_of_lt h d).trans (getD_eq_of_lt h e).symm

private theorem pcCodes_zero {gens : List (List ℕ)} {G : GenData} (hn : 0 < G.n) :
    (pcCodes gens G).getD 0 [] = onePc := by
  have hsz : (G.walk onePc (fun c s => mulPc c (gens.getD s []))).size = G.n :=
    size_walk G onePc (fun c s => mulPc c (gens.getD s []))
  show (G.walk onePc (fun c s => mulPc c (gens.getD s []))).getD 0 [] = onePc
  rw [getD_default_congr (by rw [hsz]; exact hn) [] onePc,
    walk_zero G onePc (fun c s => mulPc c (gens.getD s [])) hn]

private theorem pcCodes_succ {gens : List (List ℕ)} {G : GenData} {i : ℕ} (hi : i < G.n)
    (h0 : 0 < i) (hp : (G.parAt i).1 < i) :
    (pcCodes gens G).getD i [] =
      mulPc ((pcCodes gens G).getD (G.parAt i).1 []) (gens.getD (G.parAt i).2 []) := by
  have hsz : (G.walk onePc (fun c s => mulPc c (gens.getD s []))).size = G.n :=
    size_walk G onePc (fun c s => mulPc c (gens.getD s []))
  show (G.walk onePc (fun c s => mulPc c (gens.getD s []))).getD i [] =
    mulPc ((G.walk onePc (fun c s => mulPc c (gens.getD s []))).getD (G.parAt i).1 [])
      (gens.getD (G.parAt i).2 [])
  rw [getD_default_congr (by rw [hsz]; exact hi) [] onePc,
    getD_default_congr (by rw [hsz]; exact hp.trans hi) [] onePc,
    walk_succ G onePc (fun c s => mulPc c (gens.getD s [])) hi h0 hp]

theorem pcTabCheck_sound {Γ : Type*} [Group Γ] (ρ : Γ →* Wm) (hρ : Function.Injective ρ)
    {gens : List (List ℕ)} {G : GenData} (g : ℕ → Γ)
    (hg : ∀ s < G.ng, ρ (g s) = decPc (gens.getD s []))
    (h : pcTabCheck gens G = true) :
    Realizes G.tab (eltOf G g) ∧ eltOf G g 0 = 1 ∧
      (∀ i < G.n, ∀ s < G.ng, eltOf G g (G.rtAt i s) = eltOf G g i * g s) ∧
      ∀ i < G.n, ρ (eltOf G g i) = decPc ((pcCodes gens G).getD i []) := by
  have h' := h
  rw [pcTabCheck] at h'
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h'
  obtain ⟨⟨⟨⟨hok, _⟩, hcanon⟩, hdist⟩, hstep⟩ := h'
  have hrtOK : G.rtOK = true := by
    have h1 := hok
    simp only [ok, Bool.and_eq_true] at h1
    exact h1.1.1
  have hparOK : G.parOK = true := by
    have h1 := hok
    simp only [ok, Bool.and_eq_true] at h1
    exact h1.1.2
  obtain ⟨hn, hng, hrt, _⟩ := rtOK_spec hrtOK
  have hsize : (pcCodes gens G).size = G.n :=
    size_walk G onePc (fun c s => mulPc c (gens.getD s []))
  have hmat : ∀ i < G.n, ρ (eltOf G g i) = decPc ((pcCodes gens G).getD i []) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [pcCodes_zero hn, decPc_onePc, eltOf,
          walk_zero G (1 : Γ) (fun a s => a * g s) hn]
        exact map_one ρ
      · obtain ⟨hpp, hps, -⟩ := parOK_spec hparOK hi hpos
        have helt : eltOf G g i = eltOf G g (G.parAt i).1 * g (G.parAt i).2 := by
          rw [eltOf]
          exact walk_succ G (1 : Γ) (fun a s => a * g s) hi hpos hpp
        rw [pcCodes_succ hi hpos hpp, helt, map_mul, ih (G.parAt i).1 hpp (hpp.trans hi),
          hg (G.parAt i).2 hps, decPc_mulPc]
  have hstepElt : ∀ i < G.n, ∀ s < G.ng, eltOf G g (G.rtAt i s) = eltOf G g i * g s := by
    intro i hi s hs
    apply hρ
    rw [map_mul, hmat (G.rtAt i s) (hrt i hi s hs), hmat i hi, hg s hs, ← decPc_mulPc,
      hstep i hi s hs]
  have hinj : ∀ i < G.n, ∀ j < G.n, eltOf G g i = eltOf G g j → i = j := by
    intro i hi j hj he
    have hci : canonPc ((pcCodes gens G).getD i []) = true :=
      allCheck_spec hcanon (by rw [hsize]; exact hi)
    have hcj : canonPc ((pcCodes gens G).getD j []) = true :=
      allCheck_spec hcanon (by rw [hsize]; exact hj)
    have hdec : decPc ((pcCodes gens G).getD i []) = decPc ((pcCodes gens G).getD j []) := by
      rw [← hmat i hi, ← hmat j hj, he]
    exact distinctCheck_spec hdist (by rw [hsize]; exact hi) (by rw [hsize]; exact hj)
      (decPc_injective hci hcj hdec)
  have h0 : eltOf G g 0 = 1 := by
    rw [eltOf, walk_zero G (1 : Γ) (fun a s => a * g s) hn]
  exact ⟨realizes_tab hok h0 hstepElt hinj, h0, hstepElt, hmat⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
