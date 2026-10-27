module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.Open (GLAPPrimeCoreOf)

section Fixed

variable {S : Type*} [Group S]

theorem aut_conj_conj (w : MulAut S) (s : S) : w * MulAut.conj s * w⁻¹ = MulAut.conj (w s) := by
  ext x
  simp [MulAut.conj_apply]

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h : g ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := congrArg (fun φ : MulAut S => φ z) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at hz
    exact (mul_inv_eq_iff_eq_mul.1 hz).symm
  rwa [hZ, Subgroup.mem_bot] at h

theorem fixSub_conj (u : S) :
    CFSG.Sporadic.Schreier.fixSub (MulAut.conj u) = Subgroup.centralizer ({u} : Set S) := by
  ext x
  rw [CFSG.Sporadic.Schreier.mem_fixSub, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  · intro h
    exact mul_inv_eq_iff_eq_mul.2 h.symm

theorem map_fixSub_eq_inf (hZ : Subgroup.center S = ⊥) (w : MulAut S) :
    (CFSG.Sporadic.Schreier.fixSub w).map (MulAut.conj : S →* MulAut S) =
      (MulAut.conj : S →* MulAut S).range ⊓ Subgroup.centralizer ({w} : Set (MulAut S)) := by
  have hinj := conj_injective_of_center_eq_bot hZ
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
    Subgroup.mem_centralizer_singleton_iff, CFSG.Sporadic.Schreier.mem_fixSub]
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⟨s, rfl⟩, ?_⟩
    have h := aut_conj_conj w s
    rw [hs] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  · rintro ⟨⟨s, rfl⟩, h⟩
    refine ⟨s, ?_, rfl⟩
    have h2 := aut_conj_conj w s
    have h3 : w * MulAut.conj s * w⁻¹ = MulAut.conj s := mul_inv_eq_iff_eq_mul.2 h.symm
    rw [h3] at h2
    exact (hinj h2).symm

theorem card_inner_inf_centralizer (hZ : Subgroup.center S = ⊥) (w : MulAut S) :
    Nat.card ↥((MulAut.conj : S →* MulAut S).range ⊓ Subgroup.centralizer ({w} : Set (MulAut S))) =
      Nat.card ↥(CFSG.Sporadic.Schreier.fixSub w) := by
  rw [← map_fixSub_eq_inf hZ w]
  exact Subgroup.card_map_of_injective (K := CFSG.Sporadic.Schreier.fixSub w)
    (conj_injective_of_center_eq_bot hZ)

end Fixed

section Core

variable {S : Type} [Group S] [Finite S]

theorem index_inner_dvd_two (hZ : Subgroup.center S = ⊥)
    (hcard : Nat.card (MulAut S) ≤ 2 * Nat.card S) :
    ((MulAut.conj : S →* MulAut S).range).index ∣ 2 := by
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  have hIcard : Nat.card ((MulAut.conj : S →* MulAut S).range) = Nat.card S :=
    (Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_center_eq_bot hZ)).toEquiv).symm
  have hidx := Subgroup.index_mul_card ((MulAut.conj : S →* MulAut S).range)
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hne : ((MulAut.conj : S →* MulAut S).range).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [hIcard] at hidx
  generalize ((MulAut.conj : S →* MulAut S).range).index = i at *
  have hle : i ≤ 2 := by
    by_contra h
    push Not at h
    nlinarith
  interval_cases i <;> omega

theorem sq_mem_inner (hZ : Subgroup.center S = ⊥) (hcard : Nat.card (MulAut S) ≤ 2 * Nat.card S)
    (a : MulAut S) : a ^ 2 ∈ (MulAut.conj : S →* MulAut S).range := by
  haveI : ((MulAut.conj : S →* MulAut S).range).Normal := inner_normal S
  have h := Subgroup.pow_index_mem ((MulAut.conj : S →* MulAut S).range) a
  have h2 := index_inner_dvd_two hZ hcard
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h1
  · rw [h1, pow_one] at h
    exact Subgroup.pow_mem _ h 2
  · rw [h1] at h
    exact h

theorem core_card_le_four (hZ : Subgroup.center S = ⊥)
    (hcard : Nat.card (MulAut S) ≤ 2 * Nat.card S)
    (hcent : ∀ s : S, orderOf s = 3 →
      Nat.card ↥(Subgroup.centralizer ({s} : Set S)) = 36 ∨
        Nat.card ↥(Subgroup.centralizer ({s} : Set S)) = 54)
    (hinvol : ∀ w : MulAut S, orderOf w = 2 →
      ¬ 9 ∣ Nat.card ↥(CFSG.Sporadic.Schreier.fixSub w))
    (H : Subgroup (MulAut S)) (hH : (MulAut.conj : S →* MulAut S).range ≤ H)
    (x : MulAut S) (hxH : x ∈ H) (hx : orderOf x = 3) :
    Nat.card (GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S)))) ≤ 4 := by
  classical
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range with hIdef
  haveI hInormal : I.Normal := inner_normal S
  have hinj := conj_injective_of_center_eq_bot hZ
  have hIidx : I.index ∣ 2 := index_inner_dvd_two hZ hcard
  have hsq : ∀ a : MulAut S, a ^ 2 ∈ I := sq_mem_inner hZ hcard
  have hxI : x ∈ I := by
    have h4 : x = (x ^ 2) ^ 2 := by
      rw [← pow_mul]
      calc x = x ^ 3 * x := by rw [← hx, pow_orderOf_eq_one, one_mul]
        _ = x ^ (2 * 2) := by rw [← pow_succ]
    rw [h4]
    exact I.pow_mem (hsq x) 2
  obtain ⟨s, hs⟩ := hxI
  have hs3 : orderOf s = 3 := by
    rw [← orderOf_injective (MulAut.conj : S →* MulAut S) hinj s]
    exact hs.symm ▸ hx
  have hC0 : Nat.card ↥(I ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = 36 ∨
      Nat.card ↥(I ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = 54 := by
    rw [card_inner_inf_centralizer hZ x, ← hs, fixSub_conj]
    exact hcent s hs3
  set C : Subgroup (MulAut S) := H ⊓ Subgroup.centralizer ({x} : Set (MulAut S)) with hCdef
  have hIC : I ⊓ C = I ⊓ Subgroup.centralizer ({x} : Set (MulAut S)) := by
    ext y
    simp only [Subgroup.mem_inf, hCdef]
    constructor
    · rintro ⟨hy, -, hc⟩
      exact ⟨hy, hc⟩
    · rintro ⟨hy, hc⟩
      exact ⟨hy, hH hy, hc⟩
  have hrel : I.relIndex C ∣ 2 := (Subgroup.relIndex_dvd_index_of_normal I C).trans hIidx
  have hCcard : I.relIndex C * Nat.card ↥(I ⊓ C) = Nat.card C := Subgroup.relIndex_mul_card I C
  set N : Subgroup (MulAut S) := GLAPPrimeCoreOf 3 C with hNdef
  have hNC : N ≤ C := Subgroup.map_subtype_le _
  have hN3 : ¬ 3 ∣ Nat.card N := CFSG.LocalAnalysis.GLTheoremB.not_dvd_card_glaPPrimeCoreOf Nat.prime_three C
  have hNnorm : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    intro c hc n hn
    have h1 := Subgroup.mem_normalizer_iff.1
      (normalizer_le_normalizer_primeCoreOf 3 C (Subgroup.le_normalizer hc)) n
    exact h1.1 hn
  have hNdvd : Nat.card N ∣ Nat.card C := Subgroup.card_dvd_of_le hNC
  have hcases : Nat.card N ≤ 4 ∨ (Nat.card C = 72 ∧ Nat.card N = 8) := by
    have hk : I.relIndex C = 1 ∨ I.relIndex C = 2 := (Nat.dvd_prime Nat.prime_two).1 hrel
    rw [hIC] at hCcard
    generalize Nat.card ↥(I ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = c0 at hC0 hCcard
    generalize Nat.card C = c at hCcard hNdvd ⊢
    generalize Nat.card N = n at hN3 hNdvd ⊢
    rcases hC0 with rfl | rfl <;> rcases hk with hk | hk <;> rw [hk] at hCcard <;> subst hCcard
    all_goals
      have hle := Nat.le_of_dvd (by norm_num) hNdvd
      interval_cases n <;> omega
  rcases hcases with h | ⟨hC72, hN8⟩
  · exact h
  exfalso
  have hIC36 : Nat.card ↥(I ⊓ C) = 36 := by
    rw [hIC]
    rcases hC0 with h | h
    · exact h
    · exfalso
      rw [hIC, h, hC72] at hCcard
      have := Nat.le_of_dvd (by norm_num) hrel
      omega
  have hIN : Nat.card ↥(I ⊓ N) = 4 := by
    have h1 : I.relIndex N * Nat.card ↥(I ⊓ N) = Nat.card N := Subgroup.relIndex_mul_card I N
    have h2 : I.relIndex N ∣ 2 := (Subgroup.relIndex_dvd_index_of_normal I N).trans hIidx
    have h3 : Nat.card ↥(I ⊓ N) ∣ Nat.card ↥(I ⊓ C) :=
      Subgroup.card_dvd_of_le (inf_le_inf_left I hNC)
    rw [hN8] at h1
    rw [hIC36] at h3
    have h4 := Nat.le_of_dvd (by norm_num) h2
    generalize I.relIndex N = r at h1 h4
    generalize Nat.card ↥(I ⊓ N) = m at h1 h3 ⊢
    interval_cases r
    · omega
    · have hm : m = 8 := by omega
      subst hm
      norm_num at h3
    · omega
  have h9 : 3 ^ 2 ∣ Nat.card ↥(I ⊓ C) := by
    rw [hIC36]
    norm_num
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  set P : Subgroup (MulAut S) := P₀.map (I ⊓ C).subtype with hPdef
  have hPcard : Nat.card P = 9 := by
    rw [hPdef, Subgroup.card_map_of_injective (I ⊓ C).subtype_injective, hP₀]
    norm_num
  have hPle : P ≤ I ⊓ C := Subgroup.map_subtype_le P₀
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hPcard]; norm_num)
  have hPN : ∀ p ∈ P, ∀ n : MulAut S, n ∈ N → p * n * p⁻¹ ∈ N := fun p hp n hn =>
    hNnorm p (hPle hp).2 n hn
  have hPI : ∀ p n : MulAut S, p * n * p⁻¹ ∈ I ↔ n ∈ I := by
    intro p n
    constructor
    · intro h
      have := hInormal.conj_mem _ h p⁻¹
      simpa [mul_assoc] using this
    · intro h
      exact hInormal.conj_mem n h p
  let α := {n : ↥N // (n : MulAut S) ∉ I}
  letI : MulAction ↥P α :=
    { smul := fun p a => ⟨⟨(p : MulAut S) * a.1 * (p : MulAut S)⁻¹, hPN p p.2 a.1 a.1.2⟩,
        fun h => a.2 ((hPI p a.1).1 h)⟩
      one_smul := fun a => Subtype.ext (Subtype.ext (by
        show ((1 : ↥P) : MulAut S) * (a.1 : MulAut S) * ((1 : ↥P) : MulAut S)⁻¹ = a.1
        simp))
      mul_smul := fun p q a => Subtype.ext (Subtype.ext (by
        show ((p * q : ↥P) : MulAut S) * (a.1 : MulAut S) * ((p * q : ↥P) : MulAut S)⁻¹ =
          (p : MulAut S) * ((q : MulAut S) * (a.1 : MulAut S) * (q : MulAut S)⁻¹) *
            (p : MulAut S)⁻¹
        simp [mul_assoc])) }
  have hα4 : Nat.card α = 4 := by
    classical
    haveI : Fintype ↥N := Fintype.ofFinite _
    haveI : Fintype {n : ↥N // (n : MulAut S) ∈ I} := Fintype.ofFinite _
    haveI : Fintype α := Fintype.ofFinite _
    have h1 : Nat.card {n : ↥N // (n : MulAut S) ∈ I} = 4 := by
      have e1 : I.relIndex N * Nat.card ↥(I ⊓ N) = Nat.card N := Subgroup.relIndex_mul_card I N
      have e2 : Nat.card ↥(I.subgroupOf N) * (I.subgroupOf N).index = Nat.card ↥N :=
        Subgroup.card_mul_index (I.subgroupOf N)
      rw [hIN, hN8] at e1
      rw [hN8] at e2
      have hr0 : I.relIndex N ≠ 0 := by omega
      have e3 : Nat.card ↥(I.subgroupOf N) = 4 := by
        have hr : I.relIndex N = 2 := by omega
        have e2' : Nat.card ↥(I.subgroupOf N) * I.relIndex N = 8 := e2
        rw [hr] at e2'
        omega
      exact e3
    have h2 := Fintype.card_subtype_compl (fun n : ↥N => (n : MulAut S) ∈ I)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h2
    rw [h2, h1, hN8]
  obtain ⟨a, ha⟩ := hP3.nonempty_fixed_point_of_prime_not_dvd_card α (by rw [hα4]; norm_num)
  have hfix : ∀ p ∈ P, p * (a.1 : MulAut S) * p⁻¹ = (a.1 : MulAut S) := by
    intro p hp
    have := congrArg (fun b : α => ((b.1 : ↥N) : MulAut S)) (ha ⟨p, hp⟩)
    exact this
  set n₀ : MulAut S := (a.1 : MulAut S) with hn₀
  have hn₀N : n₀ ∈ N := a.1.2
  have hn₀I : n₀ ∉ I := a.2
  have hn₀ne : n₀ ≠ 1 := fun h => hn₀I (h ▸ I.one_mem)
  have hord : orderOf n₀ ∣ 8 := by
    have := orderOf_dvd_natCard (⟨n₀, hn₀N⟩ : ↥N)
    rwa [Subgroup.orderOf_mk, hN8] at this
  have hord2 : 2 ∣ orderOf n₀ := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show orderOf n₀ ∣ 2 ^ 3 by simpa using hord)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hn₀ne (orderOf_eq_one_iff.1 (by simpa using hk'))
    rw [hk']
    exact dvd_pow_self 2 hk0
  have hordpos : orderOf n₀ ≠ 0 := (orderOf_pos n₀).ne'
  set w : MulAut S := n₀ ^ (orderOf n₀ / 2) with hwdef
  have hw2 : orderOf w = 2 := orderOf_pow_orderOf_div hordpos hord2
  have hcomm : ∀ p ∈ P, p * w * p⁻¹ = w := by
    intro p hp
    rw [hwdef, ← conj_pow, hfix p hp]
  have hPle' : P ≤ I ⊓ Subgroup.centralizer ({w} : Set (MulAut S)) := by
    intro g hg
    exact ⟨(hPle hg).1, Subgroup.mem_centralizer_singleton_iff.2
      (mul_inv_eq_iff_eq_mul.1 (hcomm g hg))⟩
  have hdvd : 9 ∣ Nat.card ↥(I ⊓ Subgroup.centralizer ({w} : Set (MulAut S))) := by
    rw [← hPcard]
    exact Subgroup.card_dvd_of_le hPle'
  rw [hIdef, card_inner_inf_centralizer hZ w] at hdvd
  exact hinvol w hw2 hdvd

end Core

section Involutions

theorem fixSub_card_inner {N : Type*} [Group N] (hZ : Subgroup.center N = ⊥)
    (hinner : ∀ u : N, orderOf u = 2 → ¬ 9 ∣ Nat.card ↥(Subgroup.centralizer ({u} : Set N)))
    (w : MulAut N) (hw : orderOf w = 2) (hin : w ∈ (MulAut.conj : N →* MulAut N).range) :
    ¬ 9 ∣ Nat.card ↥(CFSG.Sporadic.Schreier.fixSub w) := by
  obtain ⟨u, rfl⟩ := hin
  have hinj := conj_injective_of_center_eq_bot hZ
  have h2 : MulAut.conj u ^ 2 = 1 := by
    have := pow_orderOf_eq_one (MulAut.conj u)
    rwa [hw] at this
  have hu2 : u ^ 2 = 1 := by
    apply hinj
    rw [map_pow, h2, map_one]
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hw
    omega
  have ho : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  rw [fixSub_conj]
  exact hinner u ho

theorem fixSub_card_outer {M : Type*} [Group M] (N : Subgroup M) [Finite N] (δ : M)
    (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N) (hδ2 : δ * δ ∈ N) (hcenter : Subgroup.center N = ⊥)
    (houter : ∀ g ∈ N, ¬∀ h ∈ N, δ * g * h = h * (δ * g))
    (hcard : Nat.card (MulAut N) ≤ 2 * Nat.card N)
    (hout : ∀ u, δ⁻¹ * u ∈ N → orderOf u = 2 → ¬ 9 ∣ Nat.card ↥(CFSG.Sporadic.Schreier.centralizerIn N u))
    (α : MulAut N) (hα2 : α * α = 1) (hα : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner N) :
    ¬ 9 ∣ Nat.card ↥(CFSG.Sporadic.Schreier.fixSub α) := by
  have hδ' := CFSG.Sporadic.Schreier.inv_conj_mem N hδ hδ2
  obtain ⟨g, hg, hαg⟩ := CFSG.Sporadic.Schreier.exists_eq_conj_of_outer N δ hδ hδ2 hcenter houter hcard α hα
  set u := g * δ
  have hu : δ⁻¹ * u ∈ N := by
    simpa [u, mul_assoc] using hδ' g hg
  have hu2N : u * u ∈ N := by
    have : u * u = g * (δ * g * δ⁻¹) * (δ * δ) := by simp only [u]; group
    rw [this]
    exact N.mul_mem (N.mul_mem hg (hδ g hg)) hδ2
  have hu2 : u * u = 1 := by
    have hc : (⟨u * u, hu2N⟩ : N) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut N => (φ z : M)) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply] at hz
      rw [hαg, hαg] at hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (z : M) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by rw [hz]
        _ = u * u * z := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply hα
    refine ⟨1, MulEquiv.ext fun z => Subtype.ext ?_⟩
    rw [hαg, h1]
    simp
  have ho : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have hmap := CFSG.Sporadic.Schreier.map_fixSub_conjOn N α u hαg
  have hcardeq : Nat.card ↥(CFSG.Sporadic.Schreier.fixSub α) = Nat.card ↥(CFSG.Sporadic.Schreier.centralizerIn N u) := by
    rw [← hmap, Subgroup.card_map_of_injective N.subtype_injective]
  rw [hcardeq]
  exact hout u hu ho

end Involutions

end CFSG.LocalAnalysis.GLTheoremA.CatB
