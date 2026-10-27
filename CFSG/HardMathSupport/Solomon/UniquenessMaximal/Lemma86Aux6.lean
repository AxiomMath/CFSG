module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux5
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux4

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {A : Type*} [Group A]

set_option warn.classDefReducibility false in
@[expose] def conjAction (B' : Subgroup A) : MulAction ↥B' (Subgroup A) where
  smul b H := GLBConj ((b : A)⁻¹) H
  one_smul H := by
    show GLBConj (((1 : B') : A)⁻¹) H = H
    simp [gLBConj_one]
  mul_smul b₁ b₂ H := by
    show GLBConj (((b₁ * b₂ : B') : A)⁻¹) H = GLBConj ((b₁ : A)⁻¹) (GLBConj ((b₂ : A)⁻¹) H)
    rw [gLBConj_gLBConj]
    simp [mul_inv_rev]

theorem Centerless.gLBConj {W : Subgroup A} (h : Centerless W) (g : A) :
    Centerless (GLBConj g W) := by
  intro z hz hc
  rw [mem_gLBConj] at hz
  have h1 : g * z * g⁻¹ = 1 := by
    apply h _ hz
    intro y hy
    have hy' : g⁻¹ * y * g ∈ GLBConj g W := by
      rw [mem_gLBConj]
      simpa [mul_assoc] using hy
    have := hc _ hy'
    calc g * z * g⁻¹ * y = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by rw [this]
      _ = y * (g * z * g⁻¹) := by group
  have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
  rw [this, h1]
  group

theorem gLBConj_inv_eq_iff {W : Subgroup A} {g : A} :
    GLBConj g⁻¹ W = W ↔ g ∈ Subgroup.normalizer (W : Set A) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := mem_gLBConj (g := g⁻¹) (y := g * y * g⁻¹) (H := W)
    rw [h] at this
    simpa [mul_assoc] using this.symm
  · intro hg
    ext y
    rw [mem_gLBConj]
    exact ((Subgroup.mem_normalizer_iff.1 (inv_mem hg)) y).symm

theorem card_sup_mul_card_inf_of_le_normalizer {B N : Subgroup A}
    (hBN : B ≤ Subgroup.normalizer (N : Set A)) :
    Nat.card (B ⊔ N : Subgroup A) * Nat.card (B ⊓ N : Subgroup A) = Nat.card B * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hBN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B N hBN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf B)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (B ⊔ N))
  have h3 : Nat.card (N.subgroupOf B) = Nat.card (B ⊓ N : Subgroup A) := by
    rw [← Subgroup.card_map_of_injective B.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (B ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem lt_three_pow_succ (j : ℕ) : j + 2 < 3 ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    omega

theorem Decomp.mem_normalizer_of_count [Finite A] {X : Subgroup A} {r : ℕ}
    {W : Fin (r + 1) → Subgroup A} (hD : Decomp X r W) {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcl : Centerless (W 0))
    (hinner : ∀ φ : MulAut ↥(W 0), φ ^ p = 1 → ∃ w : ↥(W 0), φ = MulAut.conj w)
    (hw : 0 < CFSG.Open.pRank p (W 0)) {B' : Subgroup A} (hB'X : B' ≤ X)
    (hB'el : IsElemAbelian p B') (hB'card : Nat.card B' = p ^ m)
    (hX : ∀ E : Subgroup A, E ≤ X → IsElemAbelian p E → Nat.card E ≤ p ^ m) :
    B' ≤ Subgroup.normalizer (W 0 : Set A) := by
  classical
  by_contra hnot
  obtain ⟨b, hbB, hbN⟩ := Set.not_subset.1 hnot
  have hp1 : 1 < p := hp.one_lt
  set w := CFSG.Open.pRank p (W 0) with hwdef
  have hWw : ∀ E : Subgroup A, E ≤ W 0 → IsElemAbelian p E → Nat.card E ≤ p ^ w := by
    intro E hE hEel
    have : Fact p.Prime := ⟨hp⟩
    have hEp : IsPGroup p E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hEel.2 g.1 g.2)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have := CFSG.SectionRank.le_pRank hp1 hE hEel hk
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos this
  have hB₀ := card_inf_normalizer_le hB'el hcl hinner hWw
  let _ := conjAction B'
  set O := MulAction.orbit ↥B' (W 0) with hO
  set Stab := MulAction.stabilizer ↥B' (W 0) with hStab
  have hsmul : ∀ (b' : B') (H : Subgroup A), b' • H = GLBConj ((b' : A)⁻¹) H := fun _ _ => rfl
  have hstab_iff : ∀ b' : B', b' ∈ Stab ↔ (b' : A) ∈ Subgroup.normalizer (W 0 : Set A) := by
    intro b'
    rw [hStab, MulAction.mem_stabilizer_iff, hsmul]
    have := gLBConj_inv_eq_iff (W := W 0) (g := (b' : A))
    rw [this]
  have hOS : Nat.card B' = Nat.card O * Nat.card Stab := by
    have e := MulAction.orbitEquivQuotientStabilizer ↥B' (W 0)
    rw [Nat.card_congr e]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup Stab
  have hStab_card : Nat.card Stab = Nat.card (B' ⊓ Subgroup.normalizer (W 0 : Set A) : Subgroup A) := by
    have : Stab.map B'.subtype = B' ⊓ Subgroup.normalizer (W 0 : Set A) := by
      ext y
      constructor
      · rintro ⟨b', hb', rfl⟩
        exact ⟨b'.2, (hstab_iff b').1 hb'⟩
      · rintro ⟨hy1, hy2⟩
        exact ⟨⟨y, hy1⟩, (hstab_iff ⟨y, hy1⟩).2 hy2, rfl⟩
    rw [← this, Subgroup.card_map_of_injective B'.subtype_injective]
  have : Nonempty O := ⟨⟨W 0, MulAction.mem_orbit_self _⟩⟩
  have hk2 : 2 ≤ Nat.card O := by
    have hpos : 0 < Nat.card O := Nat.card_pos
    by_contra hlt
    have hk1 : Nat.card O = 1 := by omega
    have hStabTop : Stab = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top]
      rw [hk1, one_mul] at hOS
      exact hOS.symm
    exact hbN ((hstab_iff ⟨b, hbB⟩).1 (hStabTop ▸ Subgroup.mem_top _))
  have hOmem : ∀ x : O, ∃ g ∈ B', (x : Subgroup A) = GLBConj g (W 0) := by
    rintro ⟨x, b', rfl⟩
    exact ⟨(b' : A)⁻¹, B'.inv_mem b'.2, rfl⟩
  choose g hgB hgx using hOmem
  have hidx : ∀ x : O, ∃ j, W j = (x : Subgroup A) := by
    intro x
    obtain ⟨j, hj⟩ := hD.perm (g x) (hB'X (hgB x)) 0
    exact ⟨j, by rw [← hj, ← hgx x]⟩
  choose idx hidx using hidx
  have : Fintype O := Fintype.ofFinite O
  have hidx_inj : Function.Injective idx := by
    intro x y hxy
    apply Subtype.ext
    rw [← hidx x, ← hidx y, hxy]
  have hcomm : Pairwise fun x y : O => ∀ a c : A, a ∈ (x : Subgroup A) → c ∈ (y : Subgroup A) →
      Commute a c := by
    intro x y hxy a c ha hc
    have hne : idx x ≠ idx y := fun h => hxy (hidx_inj h)
    rw [← hidx x] at ha
    rw [← hidx y] at hc
    exact hD.commute hne ha hc
  have hind : _root_.iSupIndep (fun x : O => (x : Subgroup A)) := by
    have := hD.iSupIndep.comp hidx_inj
    have e : (fun x : O => (x : Subgroup A)) = W ∘ idx := funext fun x => (hidx x).symm
    rw [e]
    exact this
  have hclx : ∀ x : O, Centerless (x : Subgroup A) := fun x => by
    rw [hgx x]
    exact hcl.gLBConj (g x)
  have hxX : ∀ x : O, (x : Subgroup A) ≤ X := fun x => by
    rw [← hidx x]
    exact hD.le _
  obtain ⟨E₀, hE₀W, hE₀el, hE₀card⟩ := CFSG.SectionRank.exists_pRank hp1 (W 0)
  have hEx : ∀ x : O, GLBConj (g x) E₀ ≤ (x : Subgroup A) := fun x => by
    rw [hgx x]
    exact gLBConj_mono _ hE₀W
  have hExel : ∀ x : O, IsElemAbelian p (GLBConj (g x) E₀) := fun x =>
    CFSG.SectionRank.isElemAbelian_map hE₀el _
  have hExcard : ∀ x : O, Nat.card (GLBConj (g x) E₀) = p ^ w := fun x => by
    rw [GLBConj, Subgroup.card_map_of_injective (MulAut.conj (g x)⁻¹).injective, hE₀card]
  obtain ⟨S, hSel, hSle, hScard⟩ := exists_elemAbelian_pi (V := fun x : O => (x : Subgroup A))
    (E := fun x : O => GLBConj (g x) E₀) hEx hcomm hind hExel hExcard
  set B₁ : Subgroup A := B' ⊓ Subgroup.centralizer (W 0 : Set A) with hB₁
  have hB₁el : IsElemAbelian p B₁ := isElemAbelian_mono hB'el inf_le_left
  have hB₁x : ∀ x : O, ∀ y ∈ (x : Subgroup A), ∀ z ∈ B₁, z * y = y * z := by
    intro x y hy z hz
    rw [hgx x, mem_gLBConj] at hy
    have h1 : z * (g x * y * (g x)⁻¹) = (g x * y * (g x)⁻¹) * z :=
      (Subgroup.mem_centralizer_iff.1 hz.2 _ hy).symm
    have hcomm' : z * g x = g x * z := by
      have := hB'el.1
      have h := mul_comm' (⟨z, hz.1⟩ : B') ⟨g x, hgB x⟩
      exact congrArg (fun t : ↥B' => (t : A)) h
    calc z * y = (g x)⁻¹ * (z * (g x * y * (g x)⁻¹)) * g x := by
          calc z * y = (g x)⁻¹ * (g x * z) * y := by group
            _ = (g x)⁻¹ * (z * g x) * y := by rw [hcomm']
            _ = _ := by group
      _ = (g x)⁻¹ * ((g x * y * (g x)⁻¹) * z) * g x := by rw [h1]
      _ = y * z := by
          calc _ = (g x)⁻¹ * (g x * y * (g x)⁻¹) * (z * g x) := by group
            _ = (g x)⁻¹ * (g x * y * (g x)⁻¹) * (g x * z) := by rw [hcomm']
            _ = y * z := by group
  have hSB₁ : B₁ ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    apply Subgroup.mem_bot.2
    exact eq_one_of_mem_iSup_of_centralizes hcomm hind hclx (hSle hz2)
      (fun x y hy => hB₁x x y hy z hz1)
  have hB₁S : B₁ ≤ Subgroup.centralizer (S : Set A) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : s ∈ ⨆ x : O, (x : Subgroup A) := hSle hs
    have hle : (⨆ x : O, (x : Subgroup A)) ≤ Subgroup.centralizer ({z} : Set A) := by
      refine iSup_le fun x y hy => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact hB₁x x y hy t hz
    have := Subgroup.mem_centralizer_iff.1 (hle hs') z (Set.mem_singleton z)
    exact this.symm
  have hTel : IsElemAbelian p (B₁ ⊔ S) := isElemAbelian_sup_of_commute hB₁el hSel hB₁S
  have hTX : B₁ ⊔ S ≤ X := sup_le (inf_le_left.trans hB'X) (hSle.trans (iSup_le hxX))
  have hSnorm : B₁ ≤ Subgroup.normalizer (S : Set A) :=
    hB₁S.trans (Subgroup.centralizer_le_normalizer _)
  have hTcard := card_sup_mul_card_inf_of_le_normalizer hSnorm
  rw [hSB₁, Subgroup.card_bot, mul_one, hScard] at hTcard
  have hTle := hX _ hTX hTel
  rw [hTcard, ← Nat.card_eq_fintype_card] at hTle
  have hB₁pos : 0 < Nat.card B₁ := Nat.card_pos
  have hchain : Nat.card B₁ * p ^ (w * Nat.card O) ≤ Nat.card O * (Nat.card B₁ * p ^ w) := by
    calc Nat.card B₁ * p ^ (w * Nat.card O) ≤ p ^ m := hTle
      _ = Nat.card B' := hB'card.symm
      _ = Nat.card O * Nat.card Stab := hOS
      _ = Nat.card O * Nat.card (B' ⊓ Subgroup.normalizer (W 0 : Set A) : Subgroup A) := by
          rw [hStab_card]
      _ ≤ Nat.card O * (Nat.card B₁ * p ^ w) := Nat.mul_le_mul_left _ hB₀
  obtain ⟨j, hj⟩ : ∃ j, Nat.card O = j + 2 := ⟨Nat.card O - 2, by omega⟩
  rw [hj] at hchain
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpw : 0 < p ^ w := pow_pos hp.pos w
  have h1 : (Nat.card B₁ * p ^ w) * p ^ (w * (j + 1)) ≤ (Nat.card B₁ * p ^ w) * (j + 2) := by
    have e : w * (j + 2) = w + w * (j + 1) := by ring
    rw [e, pow_add] at hchain
    calc (Nat.card B₁ * p ^ w) * p ^ (w * (j + 1)) = Nat.card B₁ * (p ^ w * p ^ (w * (j + 1))) := by
          ring
      _ ≤ (j + 2) * (Nat.card B₁ * p ^ w) := hchain
      _ = _ := by ring
  have h2 : p ^ (w * (j + 1)) ≤ j + 2 :=
    Nat.le_of_mul_le_mul_left h1 (Nat.mul_pos hB₁pos hpw)
  have h3 : 3 ^ (j + 1) ≤ p ^ (w * (j + 1)) :=
    calc 3 ^ (j + 1) ≤ p ^ (j + 1) := Nat.pow_le_pow_left hp3 _
      _ ≤ p ^ (w * (j + 1)) := Nat.pow_le_pow_right hp.pos (Nat.le_mul_of_pos_left _ hw)
  have := lt_three_pow_succ j
  omega

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
