module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
import CFSG.GroupTheory.PerfectCentralExtensionUnique
import TauCeti.Algebra.Group.Subgroup.Normalizer

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

private theorem closure_orderOf_eq_prime_eq_top {C : Type*} [Group C] [Finite C]
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hC : CFSG.IsQuasisimple C)
    (hcore : CFSG.pPrimeCore p C = ⊥) :
    Subgroup.closure {x : C | orderOf x = p} = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hCperf : Group.IsPerfect C := hC.1
  let Z : Subgroup C := Subgroup.center C
  let D : Subgroup C := Subgroup.closure {x : C | orderOf x = p}
  have hDn : D.Normal :=
    Subgroup.closure_normal_of_forall_conj_mem fun g x hx => by
      have hord : orderOf (g * x * g⁻¹) = orderOf x :=
        (SemiconjBy.orderOf_eq g (by simp [SemiconjBy, mul_assoc])).symm
      rw [Set.mem_setOf_eq] at hx ⊢
      rwa [hord]
  have hdvdC : p ∣ Nat.card C := by
    have h := (CFSG.GroupTheory.prime_corefree_quasisimple_prime_generation hC hp hcore).1
    exact h.trans (Subgroup.card_quotient_dvd_card (Subgroup.center C))
  obtain ⟨x, hxord, hxZ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      ((CFSG.Foundations.SteinbergCA.quasisimple_iff C).2.2.1.mp hC) hp hodd hdvdC
  have hxmem : x ∈ D := Subgroup.subset_closure hxord
  haveI : IsSimpleGroup (C ⧸ Subgroup.center C) := hC.2.1
  have hmap : D.map (QuotientGroup.mk' Z) = ⊤ := by
    haveI : (D.map (QuotientGroup.mk' Z)).Normal :=
      hDn.map (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.map (QuotientGroup.mk' Z)) with h | h
    · exfalso
      have hxD : (QuotientGroup.mk' Z) x ∈ D.map (QuotientGroup.mk' Z) :=
        Subgroup.mem_map_of_mem _ hxmem
      rw [h] at hxD
      exact hxZ ((QuotientGroup.eq_one_iff (N := Z) x).mp (Subgroup.mem_bot.mp hxD))
    · exact h
  have hsup : D ⊔ Z = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : (QuotientGroup.mk' Z) y ∈ D.map (QuotientGroup.mk' Z) :=
      hmap ▸ Subgroup.mem_top _
    obtain ⟨d, hd, hdy⟩ := Subgroup.mem_map.mp hy
    have hyd : (QuotientGroup.mk' Z) (d⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hdy, inv_mul_cancel]
    have hyZ : d⁻¹ * y ∈ Z := (QuotientGroup.eq_one_iff (N := Z) _).mp hyd
    have hy' : y = d * (d⁻¹ * y) := by group
    rw [hy']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right hyZ)
  have hDtop : D = ⊤ :=
    CFSG.GroupTheory.eq_top_of_sup_le_center_of_isPerfect (Z := Z) le_rfl hsup
  simpa [D] using hDtop

private theorem mem_centralizer_pCore_of_forall_orderOf_eq_prime {X : Type*} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {w : X} (hcop : Nat.Coprime (orderOf w) p)
    (hfix : ∀ x : X, orderOf x = p → x * w = w * x) :
    w ∈ Subgroup.centralizer (CFSG.pCore p X : Set X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let P : Subgroup X := CFSG.pCore p X
  haveI hPn : P.Normal := CFSG.pCore_normal
  let α : MulAut ↥P := MulAut.conjNormal (H := P) w
  have hαcop : Nat.Coprime (orderOf α) p :=
    hcop.coprime_dvd_left (orderOf_map_dvd (MulAut.conjNormal (H := P)) w)
  have hfixα : ∀ x : ↥P, x ^ p = 1 → α x = x := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1, map_one]
    · have hord : orderOf (x : X) = p := by
        have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx
        rcases (Nat.dvd_prime hp).1 h1 with h1' | h1'
        · exact absurd (orderOf_eq_one_iff.1 h1') hx1
        · rw [Subgroup.orderOf_coe, h1']
      have hcomm := hfix (x : X) hord
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      show w * (x : X) * w⁻¹ = (x : X)
      rw [← hcomm]
      group
  have hα1 : α = 1 :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.mulAut_eq_one_of_coprime_of_fix_omega
      hp2 (CFSG.pCore_isPGroup (p := p) (G := X)) hαcop hfixα
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : α ⟨y, hy⟩ = ⟨y, hy⟩ := by
    simpa [α] using congrArg (fun σ : MulAut ↥P => σ ⟨y, hy⟩) hα1
  have h2 : w * y * w⁻¹ = y := congrArg Subtype.val h1
  calc y * w = (w * y * w⁻¹) * w := by rw [h2]
    _ = w * y := by group

private theorem le_centralizer_singleton_of_isComponent {X : Type*} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) {C : Subgroup X} (hC : CFSG.IsComponent C)
    (hcore : CFSG.pPrimeCore p X = ⊥) {w : X}
    (hw : ∀ x : X, orderOf x = p → x * w = w * x) :
    C ≤ Subgroup.centralizer ({w} : Set X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hCcore : CFSG.pPrimeCore p ↥C = ⊥ :=
    CFSG.RankThreeCoreUniqueness.Helpers.cfsg_subnormal_primeComplementCore_eq_bot
      p C (CFSG.Open.IsSubnormal.top_iff.mpr hC.2) hcore
  have hgen : Subgroup.closure {x : ↥C | orderOf x = p} = ⊤ :=
    closure_orderOf_eq_prime_eq_top hp hodd hC.1 hCcore
  have hset : C.subtype '' {x : ↥C | orderOf x = p} = {x : X | x ∈ C ∧ orderOf x = p} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      change orderOf (y : X) = p
      rwa [Subgroup.orderOf_coe]
    · rintro ⟨hxC, hx⟩
      refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      change orderOf (⟨x, hxC⟩ : ↥C) = p
      rwa [← Subgroup.orderOf_coe]
  have hgenX : Subgroup.closure {x : X | x ∈ C ∧ orderOf x = p} = C := by
    rw [← hset, ← MonoidHom.map_closure, hgen, Subgroup.map_top, Subgroup.range_subtype]
  rw [← hgenX, Subgroup.closure_le]
  rintro x ⟨-, hx⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hw x hx)

private theorem mem_centralizer_layer_of_forall_orderOf_eq_prime {X : Type*} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hcore : CFSG.pPrimeCore p X = ⊥) {w : X}
    (hw : ∀ x : X, orderOf x = p → x * w = w * x) :
    w ∈ Subgroup.centralizer (CFSG.layer X : Set X) := by
  have hle : CFSG.layer X ≤ Subgroup.centralizer ({w} : Set X) := by
    rw [CFSG.layer.eq_sSup]
    exact sSup_le fun C hC => le_centralizer_singleton_of_isComponent hp hodd hC hcore hw
  have hle' : CFSG.layer X ≤ Subgroup.centralizer (Subgroup.zpowers w : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hle
  exact (Subgroup.le_centralizer_iff.mp hle') (Subgroup.mem_zpowers w)

private theorem mem_centralizer_sup_of_mem {X : Type*} [Group X] {A B : Subgroup X} [A.Normal]
    {w : X} (hA : w ∈ Subgroup.centralizer (A : Set X))
    (hB : w ∈ Subgroup.centralizer (B : Set X)) :
    w ∈ Subgroup.centralizer ((A ⊔ B : Subgroup X) : Set X) := by
  rw [Subgroup.mem_centralizer_iff] at hA hB ⊢
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  calc a * b * w = a * (b * w) := by group
    _ = a * (w * b) := by rw [hB b hb]
    _ = a * w * b := by group
    _ = w * a * b := by rw [hA a ha]
    _ = w * (a * b) := by group

private theorem commute_mk_of_le_xSub (h : TwelveCtx G M p Q H) (hL : pLayerIn p H ≤ M)
    {W : Subgroup G} (hWX : W ≤ xSub p M H) (hWH : W ≤ H) {w : G} (hw : w ∈ W) :
    ∀ x : StarGroup p H, orderOf x = p →
      x * (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) ⟨w, hWH hw⟩ =
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) ⟨w, hWH hw⟩ * x := by
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  obtain ⟨wH, hwCent, hwG⟩ := Subgroup.mem_map.mp
    (show w ∈ CFSG.AGLEmbedding.d1PlusCore p H (kStar p M H) from hWX hw)
  have hwHeq : wH = ⟨w, hWH hw⟩ := Subtype.ext hwG
  have hwbar_cent : π ⟨w, hWH hw⟩ ∈
      Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) := by
    rw [← hwHeq]
    exact Subgroup.mem_comap.mp hwCent
  have hsub : {x : StarGroup p H | orderOf x = p} ⊆ (kStar p M H : Set _) := by
    intro x hx
    rw [kStar_eq_closure_of_le h.p_prime hL]
    exact Subgroup.subset_closure hx
  have hcentS : π ⟨w, hWH hw⟩ ∈
      Subgroup.centralizer {x : StarGroup p H | orderOf x = p} :=
    Subgroup.centralizer_le hsub hwbar_cent
  exact fun x hx => Subgroup.mem_centralizer_iff.mp hcentS x hx

private theorem mk_eq_one_of_le_xSub (h : TwelveCtx G M p Q H) (hL : pLayerIn p H ≤ M)
    {W : Subgroup G} (hW : Nat.Coprime p (Nat.card W)) (hWX : W ≤ xSub p M H)
    (hWH : W ≤ H) {w : G} (hw : w ∈ W) :
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) ⟨w, hWH hw⟩ = 1 := by
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  have hcore : CFSG.pPrimeCore p (StarGroup p H) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥H) p
  have horderp := commute_mk_of_le_xSub h hL hWX hWH hw
  have hcopW : Nat.Coprime (orderOf w) p :=
    hW.symm.coprime_dvd_left (Subgroup.orderOf_dvd_natCard W hw)
  have hcopbar : Nat.Coprime (orderOf (π ⟨w, hWH hw⟩)) p := by
    refine hcopW.coprime_dvd_left ?_
    have hd := orderOf_map_dvd π (⟨w, hWH hw⟩ : ↥H)
    rw [← Subgroup.orderOf_coe] at hd
    exact hd
  have hpcent : π ⟨w, hWH hw⟩ ∈
      Subgroup.centralizer (CFSG.pCore p (StarGroup p H) : Set (StarGroup p H)) :=
    mem_centralizer_pCore_of_forall_orderOf_eq_prime h.p_prime h.p_odd hcopbar horderp
  have hlcent : π ⟨w, hWH hw⟩ ∈
      Subgroup.centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) :=
    mem_centralizer_layer_of_forall_orderOf_eq_prime h.p_prime h.p_odd hcore horderp
  have hsupcent : π ⟨w, hWH hw⟩ ∈ Subgroup.centralizer
      ((CFSG.pCore p (StarGroup p H) ⊔ CFSG.layer (StarGroup p H) :
        Subgroup (StarGroup p H)) : Set (StarGroup p H)) :=
    mem_centralizer_sup_of_mem hpcent hlcent
  have hpCore : π ⟨w, hWH hw⟩ ∈ CFSG.pCore p (StarGroup p H) :=
    centralizer_pCore_sup_layer_le h.p_prime H hsupcent
  obtain ⟨n, hn⟩ :=
    (CFSG.pCore_isPGroup (p := p) (G := StarGroup p H)).exists_orderOf_eq_pow
      ⟨π ⟨w, hWH hw⟩, hpCore⟩
  have hn' : orderOf (π ⟨w, hWH hw⟩) = p ^ n :=
    (Subgroup.orderOf_coe ⟨π ⟨w, hWH hw⟩, hpCore⟩).trans hn
  have h1 : orderOf (π ⟨w, hWH hw⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hcopbar.pow_right n) dvd_rfl (by rw [hn'])
  exact orderOf_eq_one_iff.mp h1

theorem TwelveCtx.le_relPPrimeCore_of_le_xSub (h : TwelveCtx G M p Q H)
    (hL : pLayerIn p H ≤ M) {W : Subgroup G} (hW : Nat.Coprime p (Nat.card W))
    (hWX : W ≤ xSub p M H) : W ≤ relPPrimeCore p H := by
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  have hWH : W ≤ H := hWX.trans (xSub_le_H p M H)
  intro w hw
  have h1 : π ⟨w, hWH hw⟩ = 1 := mk_eq_one_of_le_xSub h hL hW hWX hWH hw
  have h2 : (⟨w, hWH hw⟩ : ↥H) ∈ primeComplementCore (G := ↥H) p :=
    (QuotientGroup.eq_one_iff (N := primeComplementCore (G := ↥H) p) _).mp h1
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
    h.p_prime H]
  exact ⟨⟨w, hWH hw⟩, h2, rfl⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
