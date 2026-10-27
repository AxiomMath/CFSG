module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec81b
import CFSG.Goldschmidt.Steps.Sec85a
import CFSG.Goldschmidt.Steps.Sec85c
import CFSG.Walter.Bender1970.S38.NotCyclic

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

omit [Finite G] in
theorem not_isCyclic_of_card_eq_sq [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hEp : ∀ e : E, e ^ p = 1) (hEc : Nat.card E = p ^ 2) : ¬ IsCyclic E := by
  intro hcyc
  have hexp : Monoid.exponent E ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one hEp
  rw [IsCyclic.exponent_eq_card, hEc] at hexp
  have h := Nat.le_of_dvd hp.pos hexp
  have h2 : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem isCyclic_inf_centralizer_of_mem (h81 : S_G81) (h84 : S_G84) (hset : GoldSetting G S A)
    (h4 : Nat.card A = 4) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G}
    (hH : H ∈ Walter.benderM a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : G}
    (htA : t ∈ Subgroup.centralizer (A : Set G)) (ht2 : t ^ 2 = 1)
    (hta : t ∉ Subgroup.zpowers a) :
    IsCyclic (qCoreOf H p ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hnc
  obtain ⟨hHa, -, -, huniq⟩ := h81 G S A hset h4 a ha ha1 H hH
  have hPp : IsPGroup p (qCoreOf H p ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :=
    (qCoreOf_isPGroup H p).to_le inf_le_left
  obtain ⟨E, hEle, hEp, hEcard⟩ := exists_plane hp hp2 hPp hnc
  have hEpg : IsPGroup p E := IsPGroup.of_card hEcard
  have hEnc := not_isCyclic_of_card_eq_sq hp hEp hEcard
  have hEF : E ≤ CFSG.fittingSubgroupOf H :=
    hEle.trans (inf_le_left.trans (qCoreOf_le_fittingSubgroupOf H p hp))
  have hEC : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤ H := fun e he he1 => by
    have hep : e ^ p = 1 := by simpa using congrArg Subtype.val (hEp ⟨e, he⟩)
    have hcard : (Nat.card (Subgroup.zpowers e)).Prime := by
      rw [Nat.card_zpowers, orderOf_eq_prime hep he1]
      exact hp
    refine le_trans (fun y hy => ?_) (h84 G S A hset h4 a ha ha1 H hH _
      (Subgroup.zpowers_le.mpr (hEF he)) hcard)
    exact Subgroup.centralizer_le_normalizer _ (mem_centralizer_zpowers hy)
  have hat : Subgroup.zpowers a ⊔ Subgroup.zpowers t ≤ Subgroup.centralizer ({a} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp htA a ha).symm))
  have hEat : ∀ e ∈ E, Subgroup.zpowers a ⊔ Subgroup.zpowers t ≤
      Subgroup.centralizer ({e} : Set G) := fun e he => by
    have heP := (hEle he).1
    have hea : e ∈ Subgroup.centralizer ({a} : Set G) := hHa ▸ qCoreOf_le H p heP
    have het : e ∈ Subgroup.centralizer ({t} : Set G) := (hEle he).2
    exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hea).symm))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp het).symm))
  refine false_of_four hset h4 ha ha1 hH hHa htA ht2 hta fun v hv hv1 _ => ?_
  obtain ⟨M, hM, hvM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom
    (Subgroup.centralizer ({v} : Set G))).resolve_left (centralizer_ne_top hset hv1)
  have hav : a ∈ Subgroup.centralizer ({v} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp (hat hv)).symm
  have hEv : E ≤ Subgroup.centralizer ({v} : Set G) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hEat e he hv)).symm
  have hMH := huniq p hp hp2 E hEF hEpg hEnc hEC M hM
    (sup_le (Subgroup.zpowers_le.mpr (hvM hav)) (hEv.trans hvM))
  exact hMH ▸ hvM

theorem isCyclic_inf_centralizer (h81 : S_G81) (h84 : S_G84) (hset : GoldSetting G S A)
    (h4 : Nat.card A = 4) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G}
    (hH : H ∈ Walter.benderM a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : G} (htH : t ∈ H)
    (ht2 : t ^ 2 = 1) (hta : t ∉ Subgroup.zpowers a) :
    IsCyclic (qCoreOf H p ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHa := (h81 G S A hset h4 a ha ha1 H hH).1
  have ht1 : t ≠ 1 := fun h => hta (h ▸ Subgroup.one_mem _)
  have hSH : (S : Subgroup G) ≤ H := le_of_mem_benderM hset h4 ha hH
  have htp : IsPGroup 2 (Subgroup.zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1, pow_one])
  obtain ⟨h, hh, hht⟩ := Walter.exists_conj_le_sylow_of_isPGroup S hSH
    (Subgroup.zpowers_le.mpr htH) htp
  have ht'S := hht t (Subgroup.mem_zpowers t)
  have hha : h ∈ Subgroup.centralizer ({a} : Set G) := hHa ▸ hh
  have ht'a : h⁻¹ * t * h ∉ Subgroup.zpowers a := fun hmem => by
    apply hta
    have hN : h ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_zpowers hha)
    simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.mp hN _).mp hmem
  have hcyc := isCyclic_inf_centralizer_of_mem h81 h84 hset h4 ha ha1 hH hp hp2
    (le_centralizer hset h4 ht'S) (by simpa using conj_sq_eq_one (g := h⁻¹) ht2) ht'a
  have hle : qCoreOf H p ⊓ Subgroup.centralizer ({t} : Set G) ≤
      (qCoreOf H p ⊓ Subgroup.centralizer ({h⁻¹ * t * h} : Set G)).map
        (MulAut.conj h).toMonoidHom := by
    intro z hz
    refine ⟨h⁻¹ * z * h, ⟨?_, ?_⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp (le_normalizer_of_isNormalIn
        (qCoreOf_normal_in H p) (H.inv_mem hh)) z).mp hz.1
    · show h⁻¹ * z * h ∈ Subgroup.centralizer ({h⁻¹ * t * h} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hzt := Subgroup.mem_centralizer_singleton_iff.mp hz.2
      calc h⁻¹ * z * h * (h⁻¹ * t * h) = h⁻¹ * (z * t) * h := by group
        _ = h⁻¹ * (t * z) * h := by rw [hzt]
        _ = h⁻¹ * t * h * (h⁻¹ * z * h) := by group
  have := isCyclic_map_conj (K := qCoreOf H p ⊓ Subgroup.centralizer ({h⁻¹ * t * h} : Set G)) h
  exact Subgroup.isCyclic_of_le hle

end CFSG.Goldschmidt.Sec8
