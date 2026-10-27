module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsA
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1

open CFSG.Open
open scoped Pointwise

variable {Q : Type} [Group Q] [Finite Q]

theorem le_iSup_centralizer_index_two {B Y : Subgroup Q} (hB : IsElemAbelian 2 B)
    (hBY : B ≤ Subgroup.normalizer (Y : Set Q)) (hY : Odd (Nat.card Y)) :
    Y ≤ ⨆ (E : Subgroup Q) (_ : E ≤ B) (_ : Nat.card B ≤ 2 * Nat.card E),
      Y ⊓ Subgroup.centralizer (E : Set Q) := by
  by_cases hsmall : Nat.card B ≤ 2
  · refine le_trans ?_ (le_iSup_of_le ⊥ (le_iSup_of_le bot_le (le_iSup_of_le ?_ le_rfl)))
    · intro y hy
      simp [Subgroup.mem_centralizer_iff, hy]
    · simpa using hsmall
  · obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hB.isPGroup
    have hm2 : 2 ≤ m := by
      by_contra h
      apply hsmall
      have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 (m - 1)
      Nat.prime_two B Y hB (by rw [hm, Nat.sub_add_cancel (by omega)]) hBY
      (Nat.coprime_two_left.2 hY)
    refine le_of_eq_of_le hgen.symm ?_
    refine iSup_le fun S => iSup_le fun hS => ?_
    obtain ⟨hSB, hScard⟩ := hS
    refine le_iSup_of_le S (le_iSup_of_le hSB (le_iSup_of_le ?_ le_rfl))
    rw [hm, hScard]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp [pow_succ, mul_comm]

private def DA (X A : Subgroup Q) : Subgroup Q :=
  ⨆ (E : Subgroup Q) (_ : E ≤ A) (_ : Nat.card A ≤ 2 * Nat.card E),
    ⁅X ⊓ Subgroup.centralizer (E : Set Q), A⁆

private theorem commutator_le_DA {X A E : Subgroup Q} (hE : E ≤ A)
    (hcard : Nat.card A ≤ 2 * Nat.card E) :
    ⁅X ⊓ Subgroup.centralizer (E : Set Q), A⁆ ≤ DA X A :=
  le_iSup_of_le E (le_iSup_of_le hE (le_iSup_of_le hcard le_rfl))

private theorem DA_le {X N A : Subgroup Q} (hAX : A ≤ Subgroup.normalizer (X : Set Q))
    (hN : ∀ E : Subgroup Q, E ≤ A → Nat.card A ≤ 2 * Nat.card E →
      ∀ q ∈ X ⊓ Subgroup.centralizer (E : Set Q), ∀ a ∈ A, q * a * q⁻¹ * a⁻¹ ∈ N) :
    DA X A ≤ X ⊓ N := by
  refine iSup_le fun E => iSup_le fun hE => iSup_le fun hcard => le_inf ?_ ?_
  · exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.1 hAX)
  · rw [Subgroup.commutator_le]
    intro q hq a ha
    exact hN E hE hcard q hq a ha

private theorem map_conj_eq_of_mem_centralizer {A : Subgroup Q} {g : Q}
    (hg : g ∈ Subgroup.centralizer (A : Set Q)) : A.map (MulAut.conj g).toMonoidHom = A := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h := Subgroup.mem_centralizer_iff.1 hg a ha
    have : g * a * g⁻¹ = a := by rw [← h]; group
    simpa [MulAut.conj_apply, this] using ha
  · intro hy
    refine ⟨y, hy, ?_⟩
    have h := Subgroup.mem_centralizer_iff.1 hg y hy
    show g * y * g⁻¹ = y
    rw [← h]; group

private theorem conj_mem_inf_centralizer {X E : Subgroup Q} {t q : Q}
    (ht : t ∈ Subgroup.normalizer (X : Set Q)) (hq : q ∈ X ⊓ Subgroup.centralizer (E : Set Q)) :
    (MulAut.conj t).toMonoidHom q ∈
      X ⊓ Subgroup.centralizer ((E.map (MulAut.conj t).toMonoidHom : Subgroup Q) : Set Q) := by
  obtain ⟨hqX, hqE⟩ := Subgroup.mem_inf.1 hq
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 ht q).1 hqX, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨e, he, rfl⟩
  have h := Subgroup.mem_centralizer_iff.1 hqE e he
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc t * e * t⁻¹ * (t * q * t⁻¹) = t * (e * q) * t⁻¹ := by group
    _ = t * (q * e) * t⁻¹ := by rw [h]
    _ = t * q * t⁻¹ * (t * e * t⁻¹) := by group

private theorem map_conj_DA_le {X A : Subgroup Q} {t : Q}
    (ht : t ∈ Subgroup.normalizer (X : Set Q)) :
    (DA X A).map (MulAut.conj t).toMonoidHom ≤ DA X (A.map (MulAut.conj t).toMonoidHom) := by
  rw [DA, Subgroup.map_iSup]
  refine iSup_le fun E => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hE => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hcard => ?_
  rw [Subgroup.map_commutator]
  have hle : (X ⊓ Subgroup.centralizer (E : Set Q)).map (MulAut.conj t).toMonoidHom ≤
      X ⊓ Subgroup.centralizer ((E.map (MulAut.conj t).toMonoidHom : Subgroup Q) : Set Q) := by
    rintro _ ⟨q, hq, rfl⟩
    exact conj_mem_inf_centralizer ht hq
  refine (Subgroup.commutator_mono hle le_rfl).trans (commutator_le_DA (Subgroup.map_mono hE) ?_)
  rw [Subgroup.card_map_of_injective (MulAut.conj t).injective,
    Subgroup.card_map_of_injective (MulAut.conj t).injective]
  exact hcard

private theorem conj_mem_DA {X A : Subgroup Q} {g : Q} (hgX : g ∈ Subgroup.normalizer (X : Set Q))
    (hgA : g ∈ Subgroup.centralizer (A : Set Q)) {d : Q} (hd : d ∈ DA X A) :
    g * d * g⁻¹ ∈ DA X A := by
  have hmap := map_conj_DA_le (A := A) hgX
  rw [map_conj_eq_of_mem_centralizer hgA] at hmap
  exact hmap ⟨d, hd, rfl⟩

private theorem mem_normalizer_DA {X A : Subgroup Q} {g : Q}
    (hgX : g ∈ Subgroup.normalizer (X : Set Q)) (hgA : g ∈ Subgroup.centralizer (A : Set Q)) :
    g ∈ Subgroup.normalizer (DA X A : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro d
  refine ⟨conj_mem_DA hgX hgA, fun h => ?_⟩
  have := conj_mem_DA (inv_mem hgX) (inv_mem hgA) h
  simpa [mul_assoc] using this

private theorem DA_le_left {X A : Subgroup Q} (hAX : A ≤ Subgroup.normalizer (X : Set Q)) :
    DA X A ≤ X :=
  iSup_le fun E => iSup_le fun _ => iSup_le fun _ =>
    (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.1 hAX)

private theorem normalizer_inf_centralizer_of_abelian {X A E : Subgroup Q}
    (hA : IsElemAbelian 2 A) (hAX : A ≤ Subgroup.normalizer (X : Set Q)) (hE : E ≤ A) :
    A ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer (E : Set Q) : Subgroup Q) : Set Q) := by
  intro a ha
  have haE : a ∈ Subgroup.centralizer (E : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact hA.comm (hE he) ha
  rw [Subgroup.mem_normalizer_iff]
  have hX := Subgroup.mem_normalizer_iff.1 (hAX ha)
  have hC := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer haE)
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hX h, hC h]

private theorem le_sup_DA {X A : Subgroup Q} (hA : IsElemAbelian 2 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set Q)) (hX : Odd (Nat.card X)) :
    X ≤ (X ⊓ Subgroup.centralizer (A : Set Q)) ⊔ DA X A := by
  refine (le_iSup_centralizer_index_two hA hAX hX).trans ?_
  refine iSup_le fun E => iSup_le fun hE => iSup_le fun hcard => ?_
  have hodd : ¬ 2 ∣ Nat.card (X ⊓ Subgroup.centralizer (E : Set Q) : Subgroup Q) := by
    intro h2
    have := h2.trans (Subgroup.card_dvd_of_le
      (inf_le_left : X ⊓ Subgroup.centralizer (E : Set Q) ≤ X))
    exact (Nat.not_even_iff_odd.2 hX) (even_iff_two_dvd.2 this)
  have hfac :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      2 Nat.prime_two A (X ⊓ Subgroup.centralizer (E : Set Q)) hA.isPGroup hodd
      (normalizer_inf_centralizer_of_abelian hA hAX hE)
  refine le_of_eq_of_le hfac ?_
  exact sup_le ((commutator_le_DA hE hcard).trans le_sup_right)
    ((inf_le_inf_right _ inf_le_left).trans le_sup_left)

private theorem le_normalizer_DA {X A : Subgroup Q} (hA : IsElemAbelian 2 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set Q)) (hX : Odd (Nat.card X)) :
    X ≤ Subgroup.normalizer (DA X A : Set Q) := by
  refine (le_sup_DA hA hAX hX).trans (sup_le ?_ Subgroup.le_normalizer)
  intro z hz
  obtain ⟨hzX, hzA⟩ := Subgroup.mem_inf.1 hz
  exact mem_normalizer_DA (Subgroup.le_normalizer hzX) hzA

private theorem exists_mul_DA {X A : Subgroup Q} (hA : IsElemAbelian 2 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set Q)) (hX : Odd (Nat.card X)) {x : Q} (hx : x ∈ X) :
    ∃ c ∈ X ⊓ Subgroup.centralizer (A : Set Q), ∃ d ∈ DA X A, x = c * d := by
  have hDX : DA X A ≤ X := DA_le_left hAX
  have heq : X = DA X A ⊔ (X ⊓ Subgroup.centralizer (A : Set Q)) :=
    le_antisymm (by rw [sup_comm]; exact le_sup_DA hA hAX hX) (sup_le hDX inf_le_left)
  have hnormal : ((DA X A).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDX).2 (le_normalizer_DA hA hAX hX)
  obtain ⟨d, hd, c, hc, hdc⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.normal_subgroup_sup_factorization X (DA X A)
      (X ⊓ Subgroup.centralizer (A : Set Q)) hDX inf_le_left hnormal heq x⁻¹ (inv_mem hx)
  refine ⟨c⁻¹, inv_mem hc, d⁻¹, inv_mem hd, ?_⟩
  rw [← mul_inv_rev, hdc, inv_inv]

private theorem inv_mul_conj_mem_DA {X A : Subgroup Q} (hA : IsElemAbelian 2 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set Q)) (hX : Odd (Nat.card X)) {x : Q} (hx : x ∈ X)
    {a : Q} (ha : a ∈ A) : x⁻¹ * (a * x * a⁻¹) ∈ DA X A := by
  obtain ⟨c, hc, d, hd, rfl⟩ := exists_mul_DA hA hAX hX hx
  have hca : a * c = c * a := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 a ha
  have heq : (c * d)⁻¹ * (a * (c * d) * a⁻¹) = d⁻¹ * (a * d * a⁻¹) := by
    calc (c * d)⁻¹ * (a * (c * d) * a⁻¹) = d⁻¹ * c⁻¹ * (a * c) * d * a⁻¹ := by group
      _ = d⁻¹ * c⁻¹ * (c * a) * d * a⁻¹ := by rw [hca]
      _ = d⁻¹ * (a * d * a⁻¹) := by group
  have haC : a ∈ Subgroup.centralizer (A : Set Q) :=
    Subgroup.mem_centralizer_iff.2 fun b hb => hA.comm hb ha
  rw [heq]
  exact mul_mem (inv_mem hd) (conj_mem_DA (hAX ha) haC hd)

private theorem le_normalizer_of_forall {S H : Subgroup Q} (h : ∀ g ∈ S, ∀ d ∈ H, g * d * g⁻¹ ∈ H) :
    S ≤ Subgroup.normalizer (H : Set Q) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro d
  refine ⟨h g hg d, fun hd => ?_⟩
  have := h g⁻¹ (inv_mem hg) _ hd
  simpa [mul_assoc] using this

private theorem conj_mem_iSup {𝒜 : Set (Subgroup Q)} {F : Subgroup Q → Subgroup Q} {g : Q}
    (h : ∀ A ∈ 𝒜, ∀ d ∈ F A, g * d * g⁻¹ ∈ ⨆ A ∈ 𝒜, F A) :
    ∀ d ∈ ⨆ A ∈ 𝒜, F A, g * d * g⁻¹ ∈ ⨆ A ∈ 𝒜, F A := by
  intro d hd
  have hle : (⨆ A ∈ 𝒜, F A) ≤ (⨆ A ∈ 𝒜, F A).comap (MulAut.conj g).toMonoidHom :=
    iSup₂_le fun A hA e he => h A hA e he
  exact hle hd

theorem mem_centralizer_mul_of_commutators {X N : Subgroup Q} {𝒜 : Set (Subgroup Q)}
    (hX : Odd (Nat.card X)) (h𝒜 : ∀ A ∈ 𝒜, IsElemAbelian 2 A)
    (h𝒜X : ∀ A ∈ 𝒜, A ≤ Subgroup.normalizer (X : Set Q))
    (hT : IsPGroup 2 (⨆ A ∈ 𝒜, A : Subgroup Q))
    (h𝒜conj : ∀ t ∈ (⨆ A ∈ 𝒜, A : Subgroup Q), ∀ A ∈ 𝒜, A.map (MulAut.conj t).toMonoidHom ∈ 𝒜)
    (hN : ∀ A ∈ 𝒜, ∀ E : Subgroup Q, E ≤ A → Nat.card A ≤ 2 * Nat.card E →
      ∀ q ∈ X ⊓ Subgroup.centralizer (E : Set Q), ∀ a ∈ A, q * a * q⁻¹ * a⁻¹ ∈ N) :
    ∀ x ∈ X, ∃ c ∈ X ⊓ Subgroup.centralizer ((⨆ A ∈ 𝒜, A : Subgroup Q) : Set Q),
      ∃ n ∈ X ⊓ N, x = c * n := by
  set T : Subgroup Q := ⨆ A ∈ 𝒜, A
  set D : Subgroup Q := ⨆ A ∈ 𝒜, DA X A
  have hTX : T ≤ Subgroup.normalizer (X : Set Q) := iSup₂_le fun A hA => h𝒜X A hA
  have hDXN : D ≤ X ⊓ N := iSup₂_le fun A hA => DA_le (h𝒜X A hA) (hN A hA)
  have hDX : D ≤ X := hDXN.trans inf_le_left
  have hDA : ∀ A ∈ 𝒜, DA X A ≤ D := fun A hA => le_iSup₂_of_le A hA le_rfl
  have hTD : ∀ t ∈ T, ∀ d ∈ D, t * d * t⁻¹ ∈ D := by
    intro t ht
    refine conj_mem_iSup (fun A hA d hd => ?_)
    exact hDA _ (h𝒜conj t ht A hA) (map_conj_DA_le (hTX ht) ⟨d, hd, rfl⟩)
  have hTDn : T ≤ Subgroup.normalizer (D : Set Q) := le_normalizer_of_forall hTD
  let S : Subgroup Q :=
    { carrier := {t | t ∈ Subgroup.normalizer (X : Set Q) ∧
        t ∈ Subgroup.normalizer (D : Set Q) ∧ ∀ x ∈ X, x⁻¹ * (t * x * t⁻¹) ∈ D}
      mul_mem' := by
        rintro t t' ⟨ht1, ht2, ht3⟩ ⟨ht1', ht2', ht3'⟩
        refine ⟨mul_mem ht1 ht1', mul_mem ht2 ht2', fun x hx => ?_⟩
        have e : x⁻¹ * (t * t' * x * (t * t')⁻¹) =
            (x⁻¹ * (t * x * t⁻¹)) * (t * (x⁻¹ * (t' * x * t'⁻¹)) * t⁻¹) := by group
        rw [e]
        exact mul_mem (ht3 x hx) ((Subgroup.mem_normalizer_iff.1 ht2 _).1 (ht3' x hx))
      one_mem' := by
        refine ⟨one_mem _, one_mem _, fun x hx => ?_⟩
        simp
      inv_mem' := by
        rintro t ⟨ht1, ht2, ht3⟩
        refine ⟨inv_mem ht1, inv_mem ht2, fun x hx => ?_⟩
        have hy : t⁻¹ * x * t ∈ X := by
          simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem ht1) x).1 hx
        have h := ht3 _ hy
        have e : x⁻¹ * (t⁻¹ * x * t⁻¹⁻¹) = ((t⁻¹ * x * t)⁻¹ * (t * (t⁻¹ * x * t) * t⁻¹))⁻¹ := by
          group
        rw [e]
        exact inv_mem h }
  have hTS : T ≤ S := by
    refine iSup₂_le fun A hA a ha => ?_
    have hAT : A ≤ T := le_iSup₂_of_le A hA le_rfl
    exact ⟨h𝒜X A hA ha, hTDn (hAT ha),
      fun x hx => hDA A hA (inv_mul_conj_mem_DA (h𝒜 A hA) (h𝒜X A hA) hX hx ha)⟩
  intro x hx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDodd : ¬ 2 ∣ Nat.card D := by
    intro h2
    exact (Nat.not_even_iff_odd.2 hX) (even_iff_two_dvd.2 (h2.trans (Subgroup.card_dvd_of_le hDX)))
  obtain ⟨d, hd, hfix⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.exists_mul_mem_fixed_of_coset (p := 2)
      (P := T) (X := D) hT hTD hDodd (g := x) (fun t ht => (hTS ht).2.2 x hx)
  refine ⟨x * d, Subgroup.mem_inf.2 ⟨mul_mem hx (hDX hd), ?_⟩, d⁻¹,
    inv_mem (hDXN hd), by simp⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  calc b * (x * d) = b * (x * d) * b⁻¹ * b := by group
    _ = x * d * b := by rw [hfix b hb]

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1
