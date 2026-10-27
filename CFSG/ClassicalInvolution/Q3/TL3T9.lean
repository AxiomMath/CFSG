module

public import CFSG.ClassicalInvolution.Q3.TL3T8

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

structure AETwinAt (Ω : Set (Subgroup G)) (A : Subgroup G) : Prop where
  partner : ∀ {L : Subgroup G}, MaxAdj (nbrAdj Ω) A L → ∃ L' : Subgroup G,
    MaxAdj (nbrAdj Ω) A L' ∧ L' ≠ L ∧ ∀ u u' : G, IsUniqueInvolution L u →
      IsUniqueInvolution L' u' → CentX Ω A (u * u')
  sameNbr : ∀ {L L' : Subgroup G} {u u' : G}, MaxAdj (nbrAdj Ω) A L → MaxAdj (nbrAdj Ω) A L' →
    L ≠ L' → IsUniqueInvolution L u → IsUniqueInvolution L' u' → CentX Ω A (u * u') →
    ∀ L'' : Subgroup G, MaxAdj (nbrAdj Ω) A L'' → L'' ≠ L → L'' ≠ L' →
      (∀ x ∈ L, ∀ w ∈ L'', x * w = w * x) → ∀ x ∈ L', ∀ w ∈ L'', x * w = w * x
  cong : ∀ {L L' : Subgroup G} {u u' a : G}, MaxAdj (nbrAdj Ω) A L → MaxAdj (nbrAdj Ω) A L' →
    L ≠ L' → IsUniqueInvolution L u → IsUniqueInvolution L' u' → CentX Ω A (u * u') →
    IsUniqueInvolution A a → ∀ l ∈ L, ∃ l' ∈ L', l⁻¹ * l' ∈ Qz a
  yElt : ∀ {L L' : Subgroup G} {u u' : G}, MaxAdj (nbrAdj Ω) A L → MaxAdj (nbrAdj Ω) A L' →
    L ≠ L' → IsUniqueInvolution L u → IsUniqueInvolution L' u' → CentX Ω A (u * u') →
    ∃ y ∈ pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}, (∃ k : ℕ, y ^ 3 ^ k = 1) ∧
      y * u = u * y ∧ y ∈ Subgroup.normalizer (L' : Set G) ∧ (∃ l' ∈ L', y * l' ≠ l' * y) ∧
      ∀ L'' : Subgroup G, MaxAdj (nbrAdj Ω) A L'' → L'' ≠ L → L'' ≠ L' →
        (∀ x ∈ L, ∀ w ∈ L'', x * w = w * x) → ∀ w ∈ L'', y * w = w * y

omit [Finite G] in
theorem comm_of_conj_mem_mul {L : Subgroup G} {u y : G} (hu : IsUniqueInvolution L u)
    {k : ℕ} (hy3 : y ^ 3 ^ k = 1) (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (h : ∀ l ∈ L, y * l * y⁻¹ = l ∨ y * l * y⁻¹ = l * u) : ∀ l ∈ L, y * l = l * y := by
  have hyu : y * u * y⁻¹ = u := by
    have hmem : y * u * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyL u).mp hu.mem
    have hsq : (y * u * y⁻¹) * (y * u * y⁻¹) = 1 := by
      calc (y * u * y⁻¹) * (y * u * y⁻¹) = y * (u * u) * y⁻¹ := by group
        _ = 1 := by rw [hu.sq]; group
    rcases hu.unique _ hmem hsq with h1 | h1
    · exfalso
      apply hu.ne_one
      calc u = y⁻¹ * (y * u * y⁻¹) * y := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  have key : ∀ c : G, (c = 1 ∨ c = u) → y * c * y⁻¹ = c := by
    rintro c (rfl | rfl)
    · group
    · exact hyu
  have hy2 : ∀ l ∈ L, (y * y) * l = l * (y * y) := by
    intro l hl
    obtain ⟨c, hc, hlc⟩ : ∃ c : G, (c = 1 ∨ c = u) ∧ y * l * y⁻¹ = l * c := by
      rcases h l hl with h1 | h1
      · exact ⟨1, Or.inl rfl, by rw [h1, mul_one]⟩
      · exact ⟨u, Or.inr rfl, h1⟩
    have hc2 : c * c = 1 := by
      rcases hc with rfl | rfl
      · group
      · exact hu.sq
    calc (y * y) * l = (y * (y * l * y⁻¹) * y⁻¹) * (y * y) := by group
      _ = (y * (l * c) * y⁻¹) * (y * y) := by rw [hlc]
      _ = ((y * l * y⁻¹) * (y * c * y⁻¹)) * (y * y) := by group
      _ = (l * c * c) * (y * y) := by rw [hlc, key c hc]
      _ = l * (y * y) := by rw [mul_assoc l c c, hc2, mul_one]
  intro l hl
  have hpow : ∀ m : ℕ, (y * y) ^ m * l = l * (y * y) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, mul_assoc, hy2 l hl, ← mul_assoc, ih, mul_assoc]
  have hodd : (3 ^ k) % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
  have h2 : 2 * ((3 ^ k + 1) / 2) = 3 ^ k + 1 := by omega
  have hym : y = (y * y) ^ ((3 ^ k + 1) / 2) := by
    calc y = y ^ (3 ^ k) * y := by rw [hy3, one_mul]
      _ = y ^ (3 ^ k + 1) := by rw [pow_succ]
      _ = y ^ (2 * ((3 ^ k + 1) / 2)) := by rw [h2]
      _ = (y * y) ^ ((3 ^ k + 1) / 2) := by rw [pow_mul, sq]
  rw [hym]
  exact hpow _

omit [Finite G] in
theorem comm_of_mem_pSpan {P : Set (Subgroup G)} {x y : G} (hy : y ∈ pSpan P)
    (h : ∀ L ∈ P, ∀ l ∈ L, x * l = l * x) : x * y = y * x := by
  have hle : pSpan P ≤ Subgroup.centralizer ({x} : Set G) :=
    pSpan_le fun L hL l hl => Subgroup.mem_centralizer_singleton_iff.mpr (h L hL l hl).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

variable {Ω : Set (Subgroup G)} {K : Subgroup G} (hS : ThinStd Ω K)
include hS

theorem ThinStd.maxAdj_symm {M N : Subgroup G} (h : MaxAdj (nbrAdj Ω) M N) :
    MaxAdj (nbrAdj Ω) N M :=
  ⟨hS.graphFam.graph.symm h.1, orbOf_mem_maxOrbs hS.graphFam h.1 h.2⟩

theorem ThinStd.false_of_triangle_of_aeTwin
    (hall : ∀ M N : Subgroup G, MaxAdj (nbrAdj Ω) M N → ThinAt Ω M N)
    {M N N' : Subgroup G} (hTM : AETwinAt Ω M) (hTN : AETwinAt Ω N)
    (hN : MaxAdj (nbrAdj Ω) M N) (hN' : MaxAdj (nbrAdj Ω) M N') (hne : N ≠ N')
    {u u' : G} (hu : IsUniqueInvolution N u) (hu' : IsUniqueInvolution N' u')
    (hc : CentX Ω M (u * u')) (hNN' : MaxAdj (nbrAdj Ω) N N') : False := by
  obtain ⟨y, hyX, ⟨k, hy3⟩, hyu, hyN', ⟨l₀, hl₀, hl₀y⟩, hycent⟩ := hTM.yElt hN hN' hne hu hu' hc
  obtain ⟨N'', hN'', hne'', htw⟩ := hTN.partner hNN'
  obtain ⟨u'', hu''⟩ := (hS.hyp.omega1 N'' hN''.1.2.1).1
  have hc'' : CentX Ω N (u' * u'') := htw u' u'' hu' hu''
  have hNM : MaxAdj (nbrAdj Ω) N M := hS.maxAdj_symm hN
  have hMN' : M ≠ N' := fun h => hN'.1.2.2.1 h.symm
  have hyN'' : ∀ w ∈ N'', y * w = w * y := by
    have hNN''c : ∀ x ∈ N, ∀ w ∈ N'', x * w = w * x := hS.commutes_of_nbrAdj hN''.1
    by_cases hM'' : N'' = M
    · intro w hw
      rw [hM''] at hw
      refine (comm_of_mem_pSpan hyX fun J hJ j hj => ?_).symm
      exact (hS.commutes_of_nbrAdj (show MaxAdj (nbrAdj Ω) M J from hJ).1 w hw j hj)
    · by_cases hmax : MaxAdj (nbrAdj Ω) M N''
      · refine hycent N'' hmax (fun h => ?_) hne'' hNN''c
        exact hN''.1.2.2.1 h
      · have hMc : ∀ x ∈ M, ∀ w ∈ N'', x * w = w * x := by
          have := hTN.sameNbr hNN' hN'' (Ne.symm hne'') hu' hu'' hc'' M hNM hMN'
            (fun h => hM'' h.symm) (fun x hx w hw => (hS.commutes_of_nbrAdj hN'.1 w hw x hx).symm)
          exact fun x hx w hw => (this w hw x hx).symm
        have hadj : nbrAdj Ω M N'' := by
          refine ⟨hN.1.1, (mem_omegaNbr_iff hS.hyp hS.two).mpr ⟨hN''.1.2.1, hM'', ?_⟩⟩
          intro w hw
          rw [Subgroup.mem_normalizer_iff]
          intro x
          constructor
          · intro hx
            have h1 : w * x * w⁻¹ = x := by rw [← hMc x hx w hw]; group
            rw [h1]
            exact hx
          · intro hx
            have h1 : w * x * w⁻¹ = x := by
              have h2 := hMc (w * x * w⁻¹) hx w hw
              calc w * x * w⁻¹ = w⁻¹ * (w * (w * x * w⁻¹)) := by group
                _ = w⁻¹ * ((w * x * w⁻¹) * w) := by rw [h2]
                _ = x := by group
            rw [← h1]
            exact hx
        intro w hw
        refine (comm_of_mem_pSpan hyX fun J hJ j hj => ?_).symm
        have hJ' : MaxAdj (nbrAdj Ω) M J := hJ
        have hnot : N'' ∉ orbOf (nbrAdj Ω) M J := fun h => hmax ((hS.maxAdj_iff_mem_orbOf hJ').mpr h)
        exact (hS.commutes_of_nbrAdj (hS.sep hJ'.1 hadj hnot) j hj w hw).symm
  have hyC : y ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyu
  have hcong := hTN.cong hNN' hN'' (Ne.symm hne'') hu' hu'' hc'' hu
  have hact : ∀ l ∈ N', y * l * y⁻¹ = l ∨ y * l * y⁻¹ = l * u' := by
    intro l hl
    obtain ⟨l'', hl'', hq⟩ := hcong l hl
    set q := l⁻¹ * l'' with hqdef
    have hyq : y * q * y⁻¹ ∈ Qz u := (isNormalTwoIn_Qz u).2.2 y hyC q hq
    have hlq : l = l'' * q⁻¹ := by rw [hqdef]; group
    have hyl'' : y * l'' * y⁻¹ = l'' := by rw [hyN'' l'' hl'']; group
    have hx : l⁻¹ * (y * l * y⁻¹) = q * (y * q * y⁻¹)⁻¹ := by
      calc l⁻¹ * (y * l * y⁻¹) = l⁻¹ * ((y * l'' * y⁻¹) * (y * q * y⁻¹)⁻¹) := by
            rw [hlq]; group
        _ = l⁻¹ * (l'' * (y * q * y⁻¹)⁻¹) := by rw [hyl'']
        _ = q * (y * q * y⁻¹)⁻¹ := by rw [hqdef]; group
    have hxQ : l⁻¹ * (y * l * y⁻¹) ∈ Qz u := by
      rw [hx]
      exact (Qz u).mul_mem hq ((Qz u).inv_mem hyq)
    have hxN : l⁻¹ * (y * l * y⁻¹) ∈ N' :=
      N'.mul_mem (N'.inv_mem hl) ((Subgroup.mem_normalizer_iff.mp hyN' l).mp hl)
    rcases hS.eq_of_mem_Qz hNN'.1 (hall N N' hNN') hu hu' hxN hxQ with h1 | h1
    · left
      calc y * l * y⁻¹ = l * (l⁻¹ * (y * l * y⁻¹)) := by group
        _ = l := by rw [h1, mul_one]
    · right
      calc y * l * y⁻¹ = l * (l⁻¹ * (y * l * y⁻¹)) := by group
        _ = l * u' := by rw [h1]
  exact hl₀y (comm_of_conj_mem_mul hu' hy3 hyN' hact l₀ hl₀)

end CFSG.ClassicalInvolution.Q3.TC.Thin
