module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux9
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux6
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_comap {Z A' : Type*} [Group Z] [Group A'] [Finite Z] {p : ℕ} (hp : p.Prime)
    (f : Z →* A') {D : Subgroup A'} (hD : ¬ p ∣ Nat.card D) (hk : ¬ p ∣ Nat.card f.ker) :
    ¬ p ∣ Nat.card (D.comap f) := by
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(D.comap f)) p hd
  have hgp : (g : Z) ^ p = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Subtype.val this
  have hfg : f g ∈ D := g.2
  have hfgp : (⟨f g, hfg⟩ : ↥D) ^ p = 1 := Subtype.ext (by simp [← map_pow, hgp])
  have h1 : orderOf (⟨f g, hfg⟩ : ↥D) ∣ p := orderOf_dvd_of_pow_eq_one hfgp
  have h2 : orderOf (⟨f g, hfg⟩ : ↥D) ∣ Nat.card D := orderOf_dvd_natCard _
  have h3 : orderOf (⟨f g, hfg⟩ : ↥D) = 1 :=
    Nat.eq_one_of_dvd_coprimes ((Nat.Prime.coprime_iff_not_dvd hp).2 hD) h1 h2
  have h4 : f g = 1 := congrArg Subtype.val (orderOf_eq_one_iff.1 h3)
  have hgk : (g : Z) ∈ f.ker := h4
  have h5 : orderOf (⟨(g : Z), hgk⟩ : ↥f.ker) = p := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hg]
  exact hk (h5 ▸ orderOf_dvd_natCard _)

omit [Finite G] in
theorem isElemAbelian_zpowers_of_pow' {A' : Type*} [Group A'] {p : ℕ} {x : A'} (hx : x ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

namespace Decomp

variable {A : Type*} [Group A] {X : Subgroup A} {r : ℕ} {W : Fin (r + 1) → Subgroup A}
  (hD : Decomp X r W)
include hD

theorem le_normalizer_iSup : X ≤ Subgroup.normalizer ((⨆ i, W i : Subgroup A) : Set A) := by
  have key : ∀ g ∈ X, ∀ y ∈ (⨆ i, W i : Subgroup A), g * y * g⁻¹ ∈ (⨆ i, W i : Subgroup A) := by
    intro g hg
    have hle : (⨆ i, W i : Subgroup A) ≤ (⨆ i, W i : Subgroup A).comap (MulAut.conj g).toMonoidHom :=
      iSup_le fun i y hy => by
        obtain ⟨j, hj⟩ := hD.perm g⁻¹ (inv_mem hg) i
        have : g * y * g⁻¹ ∈ GLBConj g⁻¹ (W i) := by
          rw [mem_gLBConj]
          simpa [mul_assoc] using hy
        rw [hj] at this
        exact (le_iSup W j) this
    intro y hy
    exact hle hy
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun h => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ h

theorem iSup_le_normalizer : (⨆ i, W i : Subgroup A) ≤ Subgroup.normalizer (W 0 : Set A) := by
  refine iSup_le fun i => ?_
  by_cases h : i = 0
  · subst h
    exact Subgroup.le_normalizer
  · exact (hD.comm i 0 h).trans (Subgroup.centralizer_le_normalizer _)

theorem isSubnormal_of_normal {C : Subgroup A} (hCle : C ≤ W 0)
    (hC : (C.subgroupOf (W 0)).Normal) : IsSubnormal C X := by
  have hWD : W 0 ≤ (⨆ i, W i : Subgroup A) := le_iSup W 0
  have hDX : (⨆ i, W i : Subgroup A) ≤ X := iSup_le hD.le
  exact IsSubnormal.step hCle hC (IsSubnormal.step hWD
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hWD).2 hD.iSup_le_normalizer)
    (IsSubnormal.step hDX ((Subgroup.normal_subgroupOf_iff_le_normalizer hDX).2
      hD.le_normalizer_iSup) (IsSubnormal.refl X)))

end Decomp

namespace LinPkg

variable {Q N : Subgroup G} (P : LinPkg Q N)

omit [Finite G] in
theorem rB_range_le {B : Subgroup G} (hBN : B ≤ N) : (P.rB hBN).range ≤ P.ρ.range := by
  rintro _ ⟨b, rfl⟩
  exact ⟨_, rfl⟩

omit [Finite G] in
theorem rB_range_isElemAbelian {p : ℕ} {B : Subgroup G} (hBN : B ≤ N)
    (hBel : IsElemAbelian p B) : IsElemAbelian p (P.rB hBN).range := by
  have hT : IsElemAbelian p (⊤ : Subgroup ↥B) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => Subtype.ext (hBel.2 x x.2)⟩
    have := hBel.1
    exact Subtype.ext (mul_comm' a.1 b.1)
  have := CFSG.SectionRank.isElemAbelian_map hT (P.rB hBN)
  rwa [← MonoidHom.range_eq_map] at this

omit [Finite G] in
theorem card_rB_range {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hQ2 : IsPGroup 2 Q) {B : Subgroup G}
    (hBN : B ≤ N) (hBel : IsElemAbelian p B) : Nat.card (P.rB hBN).range = Nat.card B :=
  (Nat.card_congr (MonoidHom.ofInjective (P.rB_injective hp hp2 hQ2 hBN hBel)).toEquiv).symm

theorem rB_range_le_normalizer (i11 : Input11_3) (it : InputMcLaughlinTypeFacts) {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hQ2 : IsPGroup 2 Q) (hK : CFSG.Open.IsKGroup ↥N)
    {B : Subgroup G} (hBN : B ≤ N) (hBel : IsElemAbelian p B) (hBcard : Nat.card B = p ^ m)
    (hrankN : CFSG.Open.pRank p N ≤ m) (hBmax : GLAIsBmax p (B.subgroupOf N)) {r : ℕ}
    {W : Fin (r + 1) → Subgroup (MulAut P.V)} (hD : Decomp P.ρ.range r W)
    (hmc : IsMcLaughlinGroup ↥(W 0)) (hpW : p ∣ Nat.card (W 0)) :
    (P.rB hBN).range ≤ Subgroup.normalizer (W 0 : Set (MulAut P.V)) := by
  have hp1 : 1 < p := hp.one_lt
  have hB'X := P.rB_range_le hBN
  have hB'el := P.rB_range_isElemAbelian hBN hBel
  have hB'card : Nat.card (P.rB hBN).range = p ^ m := by
    rw [P.card_rB_range hp hp2 hQ2 hBN hBel, hBcard]
  have hrankX : CFSG.Open.pRank p P.ρ.range ≤ m := (P.pRank_range_le hp hp2 hQ2).trans hrankN
  have hX : ∀ E : Subgroup (MulAut P.V), E ≤ P.ρ.range → IsElemAbelian p E →
      Nat.card E ≤ p ^ m := by
    intro E hE hEel
    have : Fact p.Prime := ⟨hp⟩
    have hEp : IsPGroup p E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hEel.2 g.1 g.2)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have := CFSG.SectionRank.le_pRank hp1 hE hEel hk
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos (this.trans hrankX)
  have hfacts := it ↥(W 0) hmc
  by_cases hsolv : Group.IsSolvable ↥(W 0)
  · obtain ⟨hinner, hcenter, hprimes⟩ := hfacts.1 hsolv
    have hp3 : p = 3 := (hprimes p hp hpW).resolve_left hp2
    have hw : 0 < CFSG.Open.pRank p (W 0) := by
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(W 0)) p hpW
      have hxp : ((x : MulAut P.V)) ^ p = 1 := by
        have := pow_orderOf_eq_one x
        rw [hx] at this
        exact congrArg Subtype.val this
      have hel := isElemAbelian_zpowers_of_pow' hxp
      have hcard : Nat.card (Subgroup.zpowers (x : MulAut P.V)) = p ^ 1 := by
        rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one]
      exact CFSG.SectionRank.le_pRank hp1 (Subgroup.zpowers_le.2 x.2) hel hcard
    have hinner' : ∀ φ : MulAut ↥(W 0), φ ^ p = 1 → ∃ w : ↥(W 0), φ = MulAut.conj w := by
      subst hp3
      exact hinner
    exact hD.mem_normalizer_of_count hp hp2 (Centerless.of_center_eq_bot hcenter) hinner' hw hB'X
      hB'el hB'card hX
  · obtain ⟨⟨hsimple, hnab⟩, hprimes⟩ := hfacts.2 hsolv
    set Wc : Subgroup ↥(W 0) := ⨅ n : ℕ, derivedSeries ↥(W 0) n with hWc
    set Lt : Subgroup (MulAut P.V) := Wc.map (W 0).subtype with hLt
    have e := Wc.equivMapOfInjective (W 0).subtype (W 0).subtype_injective
    have hsimpleLt : IsSimpleGroup ↥Lt := (MulEquiv.isSimpleGroup_congr e).1 hsimple
    have hnabLt : ∃ a b : ↥Lt, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩
    have hpLt : p ∣ Nat.card Lt := by
      rw [hLt, Subgroup.card_map_of_injective (W 0).subtype_injective]
      exact hprimes p hp hp2 hpW
    have hLtW : Lt ≤ W 0 := Subgroup.map_subtype_le _
    have hnormWc : Wc.Normal := by
      rw [hWc]
      exact Subgroup.normal_iInf_normal fun n => inferInstance
    have hsn : IsSubnormal Lt P.ρ.range := by
      refine hD.isSubnormal_of_normal hLtW ?_
      rw [Subgroup.subgroupOf, hLt, Subgroup.comap_map_eq_self_of_injective
        (W 0).subtype_injective]
      exact hnormWc
    have hLtne : Lt ≠ ⊥ := by
      have := hsimpleLt
      exact (Subgroup.nontrivial_iff_ne_bot Lt).1 inferInstance
    have hnormLt := P.rB_mem_normalizer_of_simple i11 hK hp hp2 hQ2 hBN hBmax hsn hsimpleLt hnabLt
      hpLt
    rintro _ ⟨b, rfl⟩
    exact hD.mem_normalizer_of_le hLtW hLtne (hB'X ⟨b, rfl⟩) (hnormLt b)

theorem core86 (i11 : Input11_3) (i5 : Input28_5) (i14 : Input28_14)
    (it : InputMcLaughlinTypeFacts) {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 4 ≤ m)
    (hQ2 : IsPGroup 2 Q) (hO2 : pCoreOf 2 P.ρ.range = ⊥) (hK : CFSG.Open.IsKGroup ↥N)
    {B M₀ : Subgroup G} (hBN : B ≤ N) (hBel : IsElemAbelian p B) (hBcard : Nat.card B = p ^ m)
    (hrankN : CFSG.Open.pRank p N ≤ m) (hBmax : GLAIsBmax p (B.subgroupOf N))
    (hM1 : ∀ S : Subgroup G, B ≤ Subgroup.normalizer (S : Set G) → ¬ p ∣ Nat.card S → S ≤ M₀)
    (hM2 : Q ≤ M₀)
    (hM3 : ∀ E : Subgroup G, E ≤ B → 3 ≤ CFSG.Open.pRank p E →
      Subgroup.normalizer (E : Set G) ≤ M₀)
    (u₀ : N) (hτ : IsTransvection (P.ρ u₀)) : ∃ n : N, (n : G)⁻¹ * (u₀ : G) * n ∈ M₀ := by
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨r, W, hW⟩ := i5 P.V P.elem P.ρ.range hO2 (P.ρ u₀) ⟨u₀, rfl⟩ hτ
  have hD : Decomp P.ρ.range r W := Decomp.of_mcLaughlin hW
  have hτW : P.ρ u₀ ∈ W 0 := hW.2.2.2.2.2.2.1
  have hmc : ∀ i, IsMcLaughlinGroup ↥(W i) := hW.2.2.2.2.2.2.2
  by_cases hpW : p ∣ Nat.card (W 0)
  · have hnorm := P.rB_range_le_normalizer i11 it hp hp2 hQ2 hK hBN hBel hBcard hrankN hBmax hD
      (hmc 0) hpW
    have hB'X := P.rB_range_le hBN
    have hB'el := P.rB_range_isElemAbelian hBN hBel
    have hB'card : Nat.card (P.rB hBN).range = p ^ m := by
      rw [P.card_rB_range hp hp2 hQ2 hBN hBel, hBcard]
    have hrankX : CFSG.Open.pRank p P.ρ.range ≤ m := (P.pRank_range_le hp hp2 hQ2).trans hrankN
    have hrankX' : m ≤ CFSG.Open.pRank p P.ρ.range :=
      CFSG.SectionRank.le_pRank hp1 hB'X hB'el hB'card
    have hpR : CFSG.Open.pRank p P.ρ.range = m := le_antisymm hrankX hrankX'
    obtain ⟨y, hyW, hycore⟩ := i14 P.V P.elem P.ρ.range hO2 (P.ρ u₀) ⟨u₀, rfl⟩ hτ r W hW p hp hp2
      (P.rB hBN).range hB'X hB'el (by rw [hB'card, hpR]) hnorm
    rw [hpR] at hycore
    obtain ⟨w, rfl⟩ := hD.le 0 hyW
    have hmem : P.ρ (w⁻¹ * u₀ * w) ∈
        Coordinator.coreIn p (m - 1) (P.rB hBN).range P.ρ.range := by
      simpa using hycore
    have := P.coreIn_le_map hp hp2 hQ2 hBN hBel hM2 hM3 (k := m - 1) (by omega) hmem
    exact ⟨w, P.mem_of_mem_map hM2 this⟩
  · have hnot : ∀ i, ¬ p ∣ Nat.card (W i) := by
      intro i
      obtain ⟨g, -, hg⟩ := hW.2.2.2.2.1 i
      rw [← hg, GLBConj, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
      exact hpW
    have hDp : ¬ p ∣ Nat.card (⨆ i, W i : Subgroup (MulAut P.V)) := hD.not_dvd_card_iSup hp hnot
    set Y : Subgroup G := ((⨆ i, W i : Subgroup (MulAut P.V)).comap P.ρ).map N.subtype with hY
    have hYcard : ¬ p ∣ Nat.card Y := by
      rw [hY, Subgroup.card_map_of_injective N.subtype_injective]
      exact not_dvd_card_comap hp P.ρ hDp (P.not_dvd_card_ker hp hp2 hQ2)
    have hXD := hD.le_normalizer_iSup
    have hBY : B ≤ Subgroup.normalizer (Y : Set G) := by
      intro b hb
      have hbN : b ∈ N := hBN hb
      have hρb : P.ρ ⟨b, hbN⟩ ∈ Subgroup.normalizer ((⨆ i, W i : Subgroup (MulAut P.V)) :
          Set (MulAut P.V)) := hXD ⟨_, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨n, hn, rfl⟩
        refine ⟨⟨b, hbN⟩ * n * ⟨b, hbN⟩⁻¹, ?_, by simp⟩
        have := (Subgroup.mem_normalizer_iff.1 hρb (P.ρ n)).1 hn
        simpa using this
      · rintro ⟨n', hn', hn'e0⟩
        have hn'e : (n' : G) = b * y * b⁻¹ := hn'e0
        have hyN : y ∈ N := by
          have h1 : (b : G)⁻¹ * (n' : G) * b ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hbN) n'.2) hbN
          have h2 : (b : G)⁻¹ * (n' : G) * b = y := by
            rw [hn'e]; group
          rwa [h2] at h1
        refine ⟨⟨y, hyN⟩, ?_, rfl⟩
        have h3 : P.ρ (⟨b, hbN⟩⁻¹ * n' * ⟨b, hbN⟩) ∈ (⨆ i, W i : Subgroup (MulAut P.V)) := by
          have := (Subgroup.mem_normalizer_iff.1 (inv_mem hρb) (P.ρ n')).1 hn'
          simpa using this
        have h4 : (⟨y, hyN⟩ : N) = ⟨b, hbN⟩⁻¹ * n' * ⟨b, hbN⟩ := by
          apply Subtype.ext
          show y = (b : G)⁻¹ * (n' : G) * b
          rw [hn'e]; group
        rw [h4]
        exact h3
    have hYM : Y ≤ M₀ := hM1 Y hBY hYcard
    have hu₀ : (u₀ : G) ∈ Y := ⟨u₀, le_iSup W 0 hτW, rfl⟩
    exact ⟨1, by simpa using hYM hu₀⟩

end LinPkg

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
