module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271TwistNorm
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Omega

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

variable {Ω : Type*} [Group Ω] {p : ℕ} {B L : Subgroup Ω}

theorem i224T_hyp0 [Finite Ω] (hc : I224CtxT p B L) :
    L ≤ i224Adm L (i224W p B (i224K B L)) ⊤ := by
  have : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨C, hCB, hAC, -, hBcard⟩ := i224_exists_complement hc.elem
    (inf_le_left : B ⊓ Subgroup.normalizer (L : Set Ω) ≤ B)
  refine hc.gen.trans (iSup₂_le fun F hF y hy => ?_)
  have hcard : Nat.card B ≤ p * (Nat.card F * Nat.card C) := by
    calc Nat.card B = Nat.card ↥(B ⊓ Subgroup.normalizer (L : Set Ω)) * Nat.card C := hBcard
      _ ≤ (p * Nat.card F) * Nat.card C := Nat.mul_le_mul_right _ hF.2
      _ = p * (Nat.card F * Nat.card C) := by ring
  obtain ⟨n, hnW, hn, -⟩ := i224_norm_elt_tw hc hCB hAC hF.1 hcard (i224T_card_compl hc hBcard) hy
  obtain ⟨z, hz, hnz⟩ := hn 1 C.one_mem
  refine mem_i224Adm.2 ⟨(mem_i224Tw.1 hy).1, n, ⟨hnW, Subgroup.mem_top _⟩, ?_⟩
  have h1 : y⁻¹ * n = z := by rw [hnz]; group
  rw [h1, Subgroup.mem_centralizer_iff]
  intro h hh
  exact hz h (mem_i224Cj.2 (by simpa using hh))

theorem i224T_hyp1 [Finite Ω] (hc : I224CtxT p B L) {c : Ω} (hcB : c ∈ B)
    (hcA : c ∉ B ⊓ Subgroup.normalizer (L : Set Ω)) :
    L ≤ i224Adm L (i224W p B (i224K B L)) (Subgroup.centralizer (i224Cj c L : Set Ω)) := by
  classical
  have : Fact p.Prime := ⟨hc.prime⟩
  set A : Subgroup Ω := B ⊓ Subgroup.normalizer (L : Set Ω) with hA
  set W : Subgroup Ω := i224W p B (i224K B L) with hW
  have hAB : A ≤ B := inf_le_left
  obtain ⟨⟨R₃, hR₃B, hAR₃, hR₃c, hR₃card⟩, ⟨R, hRB, hAR, hcR, hRcard⟩⟩ :=
    i224_split hc.elem hAB hcB hcA
  by_cases hII : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ = l
  ·
    intro y hyL
    have hyC : y ∈ Subgroup.centralizer (A : Set Ω) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have := hII a ha y hyL
      calc a * y = (a * y * a⁻¹) * a := by group
        _ = y * a := by rw [this]
    have hyK : y ∈ i224K B L :=
      Subgroup.mem_iSup_of_mem (1 : Ω) (Subgroup.mem_iSup_of_mem B.one_mem
        (by simpa using i224_mem_cj_self (g := (1 : Ω)) hyL))
    have hyW : y ∈ W :=
      Subgroup.mem_iSup_of_mem A (Subgroup.mem_iSup_of_mem ⟨hAB, hc.index.le⟩ ⟨hyK, hyC⟩)
    have hyc : y ∈ Subgroup.centralizer (i224Cj c L : Set Ω) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hne : i224Cj (1 : Ω) L ≠ i224Cj c L := by
        intro heq
        apply hcA
        have := mem_normalizer_of_i224Cj_eq heq
        exact ⟨hcB, by simpa using this⟩
      exact (hc.dist 1 B.one_mem c hcB hne y (by simpa using i224_mem_cj_self (g := (1 : Ω)) hyL)
        u hu).symm
    refine mem_i224Adm.2 ⟨hyL, y, ⟨hyW, hyc⟩, ?_⟩
    simpa using (Subgroup.centralizer (L : Set Ω)).one_mem
  · push Not at hII
    obtain ⟨a₀, ha₀, l₀, hl₀, hne₀⟩ := hII
    set M : Subgroup Ω := i224Adm L W (Subgroup.centralizer (i224Cj c L : Set Ω)) with hM
    have hnormA : ∀ a ∈ A, a ∈ Subgroup.normalizer (L : Set Ω) := fun a ha => ha.2
    have hcardR : ∀ F : Subgroup Ω, Nat.card A ≤ p * Nat.card F →
        Nat.card B ≤ p * (Nat.card F * Nat.card R) := fun F hF => by
      calc Nat.card B = Nat.card A * Nat.card R := hRcard
        _ ≤ (p * Nat.card F) * Nat.card R := Nat.mul_le_mul_right _ hF
        _ = p * (Nat.card F * Nat.card R) := by ring
    have step1 : ∀ F : Subgroup Ω,
        (F ≤ A ∧ Nat.card A ≤ p * Nat.card F) → ∀ y ∈ i224Tw L F,
        ∀ a ∈ A, a⁻¹ * y⁻¹ * a * y ∈ M := by
      intro F hF y hy a ha
      have hcaB : c * a ∈ B := B.mul_mem hcB (hAB ha)
      have hcaA : c * a ∉ A := fun h => hcA (by
        have := A.mul_mem h (A.inv_mem ha)
        simpa using this)
      obtain ⟨-, ⟨R', hR'B, hAR', hcaR', hR'card⟩⟩ := i224_split hc.elem hAB hcaB hcaA
      have hcardR' : Nat.card B ≤ p * (Nat.card F * Nat.card R') := by
        calc Nat.card B = Nat.card A * Nat.card R' := hR'card
          _ ≤ (p * Nat.card F) * Nat.card R' := Nat.mul_le_mul_right _ hF.2
          _ = p * (Nat.card F * Nat.card R') := by ring
      have haN := hnormA a ha
      have hyL : y ∈ L := (mem_i224Tw.1 hy).1
      have hy'L : a⁻¹ * y * a ∈ L := i224_conj_mem_of_normalizer haN hyL
      have hy'T : a⁻¹ * y * a ∈ i224Tw L F := by
        refine ⟨hy'L, fun f hf => ?_⟩
        have c1 : f * a = a * f := i224_elem_comm hc.elem (hAB (hF.1 hf)) (hAB ha)
        obtain ⟨hζL, hζC⟩ := (mem_i224Tw.1 hy).2 f hf
        have e : f * (a⁻¹ * y * a) * f⁻¹ * (a⁻¹ * y * a)⁻¹ = a⁻¹ * (f * y * f⁻¹ * y⁻¹) * a := by
          calc f * (a⁻¹ * y * a) * f⁻¹ * (a⁻¹ * y * a)⁻¹
              = (f * a⁻¹) * y * (a * f⁻¹) * a⁻¹ * y⁻¹ * a := by group
            _ = (a⁻¹ * f) * y * (f⁻¹ * a) * a⁻¹ * y⁻¹ * a := by
                have h1 : f * a⁻¹ = a⁻¹ * f := by
                  calc f * a⁻¹ = a⁻¹ * (a * f) * a⁻¹ := by group
                    _ = a⁻¹ * (f * a) * a⁻¹ := by rw [c1]
                    _ = a⁻¹ * f := by group
                have h2 : a * f⁻¹ = f⁻¹ * a := by
                  calc a * f⁻¹ = f⁻¹ * (f * a) * f⁻¹ := by group
                    _ = f⁻¹ * (a * f) * f⁻¹ := by rw [c1]
                    _ = f⁻¹ * a := by group
                rw [h1, h2]
            _ = a⁻¹ * (f * y * f⁻¹ * y⁻¹) * a := by group
        rw [e]
        refine ⟨i224_conj_mem_of_normalizer haN hζL, ?_⟩
        have := i224_conj_mem_centralizer ((Subgroup.normalizer (L : Set Ω)).inv_mem haN) hζC
        simpa using this
      obtain ⟨n, hnW, hn, -⟩ := i224_norm_elt_tw hc hRB hAR hF.1 (hcardR F hF.2)
        (i224T_card_compl hc hRcard) hy
      obtain ⟨n', hn'W, hn', -⟩ := i224_norm_elt_tw hc hR'B hAR' hF.1 hcardR'
        (i224T_card_compl hc hR'card) hy'T
      obtain ⟨z₁, hz₁, hnz₁⟩ := hn 1 R.one_mem
      obtain ⟨z₂, hz₂, hnz₂⟩ := hn c hcR
      obtain ⟨w₁, hw₁, hn'w₁⟩ := hn' 1 R'.one_mem
      obtain ⟨w₂, hw₂, hn'w₂⟩ := hn' (c * a) hcaR'
      have hcjca : i224Cj (c * a) L = i224Cj c L := by
        rw [i224Cj_mul, i224Cj_of_mem_normalizer haN]
      have e1 : (c * a) * (a⁻¹ * y * a) * (c * a)⁻¹ = c * y * c⁻¹ := by group
      have hxL : a⁻¹ * y⁻¹ * a * y ∈ L := by
        have : a⁻¹ * y⁻¹ * a * y = (a⁻¹ * y * a)⁻¹ * y := by group
        rw [this]
        exact L.mul_mem (L.inv_mem hy'L) hyL
      have hz₂C := i224_mem_centralizer_of_cj hz₂
      have hw₂C : w₂ ∈ Subgroup.centralizer (i224Cj c L : Set Ω) :=
        i224_mem_centralizer_of_cj (fun u hu => hw₂ u (by rw [hcjca]; exact hu))
      have hw₁C : w₁ ∈ Subgroup.centralizer (L : Set Ω) :=
        Subgroup.mem_centralizer_iff.2 fun h hh => hw₁ h (mem_i224Cj.2 (by simpa using hh))
      have hz₁C : z₁ ∈ Subgroup.centralizer (L : Set Ω) :=
        Subgroup.mem_centralizer_iff.2 fun h hh => hz₁ h (mem_i224Cj.2 (by simpa using hh))
      refine mem_i224Adm.2 ⟨hxL, n'⁻¹ * n, ⟨W.mul_mem (W.inv_mem hn'W) hnW, ?_⟩, ?_⟩
      · have hq : n'⁻¹ * n = w₂⁻¹ * z₂ := by
          rw [hnz₂, hn'w₂, e1]; group
        rw [hq]
        exact (Subgroup.centralizer (i224Cj c L : Set Ω)).mul_mem
          ((Subgroup.centralizer (i224Cj c L : Set Ω)).inv_mem hw₂C) hz₂C
      · have hq : n'⁻¹ * n = w₁⁻¹ * (a⁻¹ * y⁻¹ * a * y) * z₁ := by
          rw [hnz₁, hn'w₁]; group
        have hxw : Commute (a⁻¹ * y⁻¹ * a * y) w₁ := hw₁ _ (mem_i224Cj.2 (by simpa using hxL))
        have h2 : (a⁻¹ * y⁻¹ * a * y)⁻¹ * (n'⁻¹ * n) = w₁⁻¹ * z₁ := by
          rw [hq]
          calc (a⁻¹ * y⁻¹ * a * y)⁻¹ * (w₁⁻¹ * (a⁻¹ * y⁻¹ * a * y) * z₁)
              = (a⁻¹ * y⁻¹ * a * y)⁻¹ * ((a⁻¹ * y⁻¹ * a * y) * w₁⁻¹) * z₁ := by
                rw [hxw.inv_right.eq]; group
            _ = w₁⁻¹ * z₁ := by group
        rw [h2]
        exact (Subgroup.centralizer (L : Set Ω)).mul_mem
          ((Subgroup.centralizer (L : Set Ω)).inv_mem hw₁C) hz₁C
    have step2 : ∀ F : Subgroup Ω,
        (F ≤ A ∧ Nat.card A ≤ p * Nat.card F) → ∀ y ∈ i224Tw L F,
        ∀ x ∈ M, y * x * y⁻¹ ∈ M := by
      intro F hF y hy x hx
      have hyL : y ∈ L := (mem_i224Tw.1 hy).1
      obtain ⟨n, hnW, hn, -⟩ := i224_norm_elt_tw hc hRB hAR hF.1 (hcardR F hF.2)
        (i224T_card_compl hc hRcard) hy
      obtain ⟨z₁, hz₁, hnz₁⟩ := hn 1 R.one_mem
      obtain ⟨z₂, hz₂, hnz₂⟩ := hn c hcR
      obtain ⟨hxL, q, hq, hxq⟩ := mem_i224Adm.1 hx
      have hz₁C : z₁ ∈ Subgroup.centralizer (L : Set Ω) :=
        Subgroup.mem_centralizer_iff.2 fun h hh => hz₁ h (mem_i224Cj.2 (by simpa using hh))
      have hz₂C := i224_mem_centralizer_of_cj hz₂
      have hn' : n = y * z₁ := by rw [hnz₁]; group
      have hnN : n ∈ Subgroup.normalizer (L : Set Ω) := by
        rw [hn']
        exact Subgroup.mul_mem _ (Subgroup.le_normalizer hyL)
          (Subgroup.centralizer_le_normalizer (L : Set Ω) hz₁C)
      have hnN' : n ∈ Subgroup.normalizer ((i224Cj c L : Subgroup Ω) : Set Ω) := by
        rw [hnz₂]
        exact Subgroup.mul_mem _ (Subgroup.le_normalizer (i224_mem_cj_self hyL))
          (Subgroup.centralizer_le_normalizer ((i224Cj c L : Subgroup Ω) : Set Ω) hz₂C)
      refine mem_i224Adm.2 ⟨L.mul_mem (L.mul_mem hyL hxL) (L.inv_mem hyL), n * q * n⁻¹,
        ⟨W.mul_mem (W.mul_mem hnW hq.1) (W.inv_mem hnW), i224_conj_mem_centralizer hnN' hq.2⟩, ?_⟩
      have hcx : x * z₁ = z₁ * x := hz₁ x (mem_i224Cj.2 (by simpa using hxL))
      have hxn : y * x * y⁻¹ = n * x * n⁻¹ := by
        rw [hn']
        calc y * x * y⁻¹ = y * (x * z₁) * z₁⁻¹ * y⁻¹ := by group
          _ = y * (z₁ * x) * z₁⁻¹ * y⁻¹ := by rw [hcx]
          _ = y * z₁ * x * (y * z₁)⁻¹ := by group
      have : (y * x * y⁻¹)⁻¹ * (n * q * n⁻¹) = n * (x⁻¹ * q) * n⁻¹ := by rw [hxn]; group
      rw [this]
      exact i224_conj_mem_centralizer hnN hxq
    have hLN : L ≤ Subgroup.normalizer (M : Set Ω) := by
      refine hc.gen.trans (iSup₂_le fun F hF y hy => ?_)
      refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => step2 F hF y hy x hx, fun hx => ?_⟩
      have := step2 F hF y⁻¹ ((i224Tw L F).inv_mem hy) _ hx
      have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
      rw [e] at this
      exact this
    let T : Subgroup Ω :=
      { carrier := {l | l ∈ L ∧ a₀⁻¹ * l⁻¹ * a₀ * l ∈ M}
        mul_mem' := by
          rintro l m ⟨hl, hlM⟩ ⟨hm, hmM⟩
          refine ⟨L.mul_mem hl hm, ?_⟩
          have e : a₀⁻¹ * (l * m)⁻¹ * a₀ * (l * m) =
              (a₀⁻¹ * m⁻¹ * a₀ * m) * (m⁻¹ * (a₀⁻¹ * l⁻¹ * a₀ * l) * m) := by group
          rw [e]
          refine M.mul_mem hmM ?_
          have := (Subgroup.mem_normalizer_iff.1 (hLN (L.inv_mem hm)) _).1 hlM
          simpa using this
        one_mem' := ⟨L.one_mem, by simpa using M.one_mem⟩
        inv_mem' := by
          rintro l ⟨hl, hlM⟩
          refine ⟨L.inv_mem hl, ?_⟩
          have e : a₀⁻¹ * l⁻¹⁻¹ * a₀ * l⁻¹ = l * (a₀⁻¹ * l⁻¹ * a₀ * l)⁻¹ * l⁻¹ := by group
          rw [e]
          have := (Subgroup.mem_normalizer_iff.1 (hLN hl) _).1 (M.inv_mem hlM)
          simpa using this }
    have hLT : L ≤ T := hc.gen.trans
      (iSup₂_le fun F hF y hy => show y ∈ T from ⟨(mem_i224Tw.1 hy).1, step1 F hF y hy a₀ ha₀⟩)
    have ha₀N : a₀⁻¹ ∈ Subgroup.normalizer (L : Set Ω) :=
      (Subgroup.normalizer (L : Set Ω)).inv_mem (hnormA a₀ ha₀)
    have hne : ∃ l ∈ L, a₀⁻¹ * l * a₀⁻¹⁻¹ ≠ l := by
      refine ⟨a₀ * l₀ * a₀⁻¹, (Subgroup.mem_normalizer_iff.1 (hnormA a₀ ha₀) l₀).1 hl₀, ?_⟩
      intro h
      apply hne₀
      have e : a₀⁻¹ * (a₀ * l₀ * a₀⁻¹) * a₀⁻¹⁻¹ = l₀ := by group
      rw [e] at h
      exact h.symm
    refine (i224_gen hc.quasi ha₀N hne).trans ((Subgroup.closure_le M).2 ?_)
    rintro _ ⟨l, hl, rfl⟩
    have := (hLT (L.inv_mem hl)).2
    simpa using this

theorem i224T_omega [Finite Ω] (hc : I224CtxT p B L) : i224K B L ≤ i224W p B (i224K B L) := by
  classical
  have : Fact p.Prime := ⟨hc.prime⟩
  set A : Subgroup Ω := B ⊓ Subgroup.normalizer (L : Set Ω) with hA
  set W : Subgroup Ω := i224W p B (i224K B L) with hW
  have hAB : A ≤ B := inf_le_left
  obtain ⟨C, hCB, hAC, hAsup, -⟩ := i224_exists_complement hc.elem hAB
  haveI : Fintype ↥C := Fintype.ofFinite _
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => i224_elem_comm hc.elem hx hy
  have hKconj : ∀ b ∈ B, ∀ x ∈ i224K B L, b * x * b⁻¹ ∈ i224K B L :=
    fun b hb x hx => i224K_conj hb hx
  have hWconj : ∀ b ∈ B, ∀ w ∈ W, b * w * b⁻¹ ∈ W :=
    fun b hb w hw => i224W_conj hc.elem hKconj hb hw
  let Lf : ↥C → Subgroup Ω := fun i => i224Cj (i : Ω) L
  have hne : ∀ i c : ↥C, i ≠ c → i224Cj (i : Ω) L ≠ i224Cj (c : Ω) L := by
    intro i c hic heq
    have h1 := mem_normalizer_of_i224Cj_eq heq
    have h2 : (i : Ω)⁻¹ * c ∈ A ⊓ C :=
      ⟨⟨B.mul_mem (B.inv_mem (hCB i.2)) (hCB c.2), h1⟩, C.mul_mem (C.inv_mem i.2) c.2⟩
    rw [hAC, Subgroup.mem_bot] at h2
    exact hic (Subtype.ext (inv_mul_eq_one.1 h2))
  have hcomm : ∀ i c : ↥C, i ≠ c → ∀ x ∈ Lf i, ∀ y ∈ Lf c, x * y = y * x := fun i c hic =>
    hc.dist i (hCB i.2) c (hCB c.2) (hne i c hic)
  have hperf : ∀ i, ⁅Lf i, Lf i⁆ = Lf i := by
    intro i
    have := Subgroup.map_commutator (f := (MulAut.conj (i : Ω)).toMonoidHom) L L
    rw [i224_perfect hc.quasi] at this
    exact this.symm
  have hcjK : ∀ b ∈ B, ∃ i : ↥C, i224Cj b L = Lf i := by
    intro b hb
    rw [← hAsup] at hb
    obtain ⟨x, hx, y, hy, rfl⟩ := i224_mem_sup_of_comm (fun x hx y hy => hBc x (hAB hx) y (hCB hy)) hb
    refine ⟨⟨y, hy⟩, ?_⟩
    have : x * y = y * x := hBc x (hAB hx) y (hCB hy)
    show i224Cj (x * y) L = i224Cj y L
    rw [this, i224Cj_mul, i224Cj_of_mem_normalizer hx.2]
  have hKle : i224K B L ≤ ⨆ i, Lf i := by
    refine iSup₂_le fun b hb => ?_
    obtain ⟨i, hi⟩ := hcjK b hb
    rw [hi]
    exact le_iSup Lf i
  have hWM : W ≤ ⨆ i, Lf i := by
    refine le_trans ?_ hKle
    exact iSup₂_le fun E _ => inf_le_left
  have hH0 : ∀ i : ↥C, Lf i ≤ i224Adm (Lf i) W ⊤ := by
    intro i x hx
    have hx₀ : (i : Ω)⁻¹ * x * i ∈ L := mem_i224Cj.1 hx
    have h1 := i224Adm_conj (H := L) (Q := ⊤) (Q' := ⊤) (i : Ω) (hWconj i (hCB i.2))
      (fun q _ => Subgroup.mem_top _) (i224T_hyp0 hc hx₀)
    have e : (i : Ω) * ((i : Ω)⁻¹ * x * i) * (i : Ω)⁻¹ = x := by group
    rw [e] at h1
    exact h1
  have hH1 : ∀ i c : ↥C, i ≠ c →
      Lf i ≤ i224Adm (Lf i) W (Subgroup.centralizer ((Lf c : Subgroup Ω) : Set Ω)) := by
    intro i c hic x hx
    have hx₀ : (i : Ω)⁻¹ * x * i ∈ L := mem_i224Cj.1 hx
    have hc'B : (i : Ω)⁻¹ * c ∈ B := B.mul_mem (B.inv_mem (hCB i.2)) (hCB c.2)
    have hc'A : (i : Ω)⁻¹ * c ∉ B ⊓ Subgroup.normalizer (L : Set Ω) := by
      intro h
      have h2 : (i : Ω)⁻¹ * c ∈ A ⊓ C := ⟨h, C.mul_mem (C.inv_mem i.2) c.2⟩
      rw [hAC, Subgroup.mem_bot] at h2
      exact hic (Subtype.ext (inv_mul_eq_one.1 h2))
    have e1 : i224Cj (i : Ω) (i224Cj ((i : Ω)⁻¹ * c) L) = Lf c := by
      show _ = i224Cj (c : Ω) L
      rw [← i224Cj_mul, mul_inv_cancel_left]
    have h1 := i224Adm_conj (H := L) (Q := Subgroup.centralizer (i224Cj ((i : Ω)⁻¹ * c) L : Set Ω))
      (Q' := Subgroup.centralizer ((Lf c : Subgroup Ω) : Set Ω)) (i : Ω)
      (hWconj i (hCB i.2))
      (fun q hq => by
        have := i224_conj_centralizer (b := (i : Ω)) hq
        rw [e1] at this
        exact this)
      (i224T_hyp1 hc hc'B hc'A hx₀)
    have e : (i : Ω) * ((i : Ω)⁻¹ * x * i) * (i : Ω)⁻¹ = x := by group
    rw [e] at h1
    exact h1
  have hall := i224_iso Lf hcomm hperf W hWM hH0 hH1
  refine iSup₂_le fun b hb => ?_
  obtain ⟨i, hi⟩ := hcjK b hb
  rw [hi]
  exact hall i

end CFSG.HardMathSupport.Solomon.Coordinator
