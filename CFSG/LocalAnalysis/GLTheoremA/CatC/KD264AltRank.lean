module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltInner
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Rank

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Inner

variable {Y : Type} [Group Y] [Finite Y]

theorem isElemAbelian_map {p : ℕ} {A : Type*} [Group A] {f : A →* Y} (hf : Function.Injective f)
    {S : Subgroup A} (hS : IsElemAbelian p S) : IsElemAbelian p (S.map f) := by
  have hcomm : ∀ u ∈ S.map f, ∀ v ∈ S.map f, u * v = v * u := by
    intro u hu v hv
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hu
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hv
    have hst : s * t = t * s := by
      have := hS.1.is_comm.comm (⟨s, hs⟩ : S) ⟨t, ht⟩
      exact congrArg Subtype.val this
    rw [← map_mul, ← map_mul, hst]
  refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, ?_⟩
  intro x hx
  obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 hx
  rw [← hsx, ← map_pow, hS.2 s hs, map_one]

theorem map_ker_psiHom {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 5 ≤ n)
    (K : Subgroup Y) (hK : K.Normal) (e : K ≃* alternatingGroup (Fin n)) (B : Subgroup Y)
    (hB : IsElemAbelian p B) :
    (psiHom K hK e hp hp2 hn B (fun b hb => hB.2 b hb)).ker.map B.subtype =
      B ⊓ Subgroup.centralizer (K : Set Y) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hb1 : psiHom K hK e hp hp2 hn B (fun b hb => hB.2 b hb) b = 1 := hb
    have hcen := (psiHom_eq_one_iff K hK e hp hp2 hn B (fun b hb => hB.2 b hb) b).1 hb1
    exact ⟨b.2, hcen⟩
  · rintro ⟨hyB, hcen⟩
    refine ⟨⟨y, hyB⟩, ?_, rfl⟩
    exact (psiHom_eq_one_iff K hK e hp hp2 hn B (fun b hb => hB.2 b hb) ⟨y, hyB⟩).2 hcen

theorem card_inf_centralizer_eq_ker {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 5 ≤ n)
    (K : Subgroup Y) (hK : K.Normal) (e : K ≃* alternatingGroup (Fin n)) (B : Subgroup Y)
    (hB : IsElemAbelian p B) :
    Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) =
      Nat.card (psiHom K hK e hp hp2 hn B (fun b hb => hB.2 b hb)).ker := by
  rw [← map_ker_psiHom hp hp2 hn K hK e B hB, Subgroup.card_map_of_injective B.subtype_injective]

theorem card_le_range_of_elemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 5 ≤ n)
    (K : Subgroup Y) (hK : K.Normal) (hZ : Subgroup.center ↥K = ⊥)
    (e : K ≃* alternatingGroup (Fin n)) (B : Subgroup Y) (hB : IsElemAbelian p B)
    (hmax : IsMaxRankIn p B ⊤) (S : Subgroup (alternatingGroup (Fin n)))
    (hS : IsElemAbelian p S) :
    Nat.card S ≤ Nat.card (psiHom K hK e hp hp2 hn B (fun b hb => hB.2 b hb)).range := by
  classical
  set ψ := psiHom K hK e hp hp2 hn B (fun b hb => hB.2 b hb) with hψ
  let f : alternatingGroup (Fin n) →* Y := K.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.symm.injective
  set S' : Subgroup Y := S.map f with hS'def
  set C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hCdef
  have hS' : IsElemAbelian p S' := isElemAbelian_map hf hS
  have hC : IsElemAbelian p C := isElemAbelian_mono hB inf_le_left
  have hS'K : ∀ y ∈ S', y ∈ K := by
    intro y hy
    obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact (e.symm s).2
  have hSC : S' ≤ Subgroup.centralizer (C : Set Y) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcK : c ∈ Subgroup.centralizer (K : Set Y) := hc.2
    rw [Subgroup.mem_centralizer_iff] at hcK
    exact (hcK y (hS'K y hy)).symm
  have hT : IsElemAbelian p (S' ⊔ C) :=
    CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_sup_of_commute hS' hC hSC
  have hTle : Nat.card ↥(S' ⊔ C) ≤ Nat.card B := hmax (S' ⊔ C) le_top hT
  have hCN : C ≤ Subgroup.normalizer (S' : Set Y) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hcK : c ∈ Subgroup.centralizer (K : Set Y) := hc.2
    rw [Subgroup.mem_centralizer_iff] at hcK
    have key : y ∈ K → c * y * c⁻¹ = y := fun hyK => by
      have hcomm : c * y = y * c := (hcK y hyK).symm
      rw [hcomm]
      group
    constructor
    · intro hy
      rw [key (hS'K y hy)]
      exact hy
    · intro hy
      have hyK' : c * y * c⁻¹ ∈ K := hS'K _ hy
      have hyK : y ∈ K := by
        have h1 := hK.conj_mem _ hyK' c⁻¹
        have h2 : c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y := by group
        rwa [h2] at h1
      rw [← key hyK]
      exact hy
  have hinf : S' ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyK : y ∈ K := hS'K y hy.1
    have hcen : (⟨y, hyK⟩ : K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hc : y ∈ Subgroup.centralizer (K : Set Y) := hy.2.2
      rw [Subgroup.mem_centralizer_iff] at hc
      exact hc g g.2
    rw [hZ, Subgroup.mem_bot] at hcen
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hcen
  have hS'card : Nat.card S' = Nat.card S := Subgroup.card_map_of_injective hf
  have hprod := card_sup_mul_card_inf_of_le_normalizer hCN
  rw [hinf, Subgroup.card_bot, mul_one, hS'card] at hprod
  have hCker : Nat.card C = Nat.card ψ.ker := card_inf_centralizer_eq_ker hp hp2 hn K hK e B hB
  have hkr := Subgroup.card_ker_mul_card_range ψ
  have hkr := Subgroup.card_ker_mul_card_range ψ
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hmain : Nat.card S * Nat.card C ≤ Nat.card ψ.range * Nat.card C := by
    calc Nat.card S * Nat.card C = Nat.card ↥(S' ⊔ C) := hprod.symm
      _ ≤ Nat.card B := hTle
      _ = Nat.card ψ.ker * Nat.card ψ.range := hkr.symm
      _ = Nat.card ψ.range * Nat.card C := by rw [← hCker]; ring
  exact Nat.le_of_mul_le_mul_right hmain hCpos

end CFSG.LocalAnalysis.GLTheoremA.KD264Rank
