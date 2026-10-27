module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLiftLocal
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

section Pairing

variable {Y T : Type*} [Group Y] [Group T] {φ : Y →* T}

theorem liftComm_eq_one_of_mem_zpowers (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {s z : T}
    (hz : z ∈ Subgroup.zpowers s) : CFSG.RankThree.Classical2.liftComm φ hφ s z = 1 := by
  have hS : ∀ u ∈ ({s} : Set T), ∀ v ∈ ({s} : Set T), Commute u v := by
    intro u hu v hv
    rw [Set.mem_singleton_iff] at hu hv
    rw [hu, hv]
  have h1 : ∀ u ∈ ({s} : Set T), ∀ v ∈ ({s} : Set T),
      CFSG.RankThree.Classical2.liftComm φ hφ u v = 1 := by
    intro u hu v hv
    rw [Set.mem_singleton_iff] at hu hv
    rw [hu, hv]
    exact CFSG.RankThree.Classical2.liftComm_self hφ s
  have hs : s ∈ Subgroup.closure ({s} : Set T) := Subgroup.subset_closure rfl
  have hz' : z ∈ Subgroup.closure ({s} : Set T) := by
    rwa [← Subgroup.zpowers_eq_closure]
  exact CFSG.RankThree.CentralCover.liftComm_eq_one_of_mem_closure hφ hker hS h1 hs hz'

theorem liftComm_eq_one_of_conj_inv_of_mem_zpowers (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {s t g : T}
    (hst : Commute s t) (hsp : s ^ p = 1) (hgs : g * s * g⁻¹ = s⁻¹)
    (hgt : g * t * g⁻¹ * t⁻¹ ∈ Subgroup.zpowers s) :
    CFSG.RankThree.Classical2.liftComm φ hφ s t = 1 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set c := CFSG.RankThree.Classical2.liftComm φ hφ s t with hc
  set z : T := g * t * g⁻¹ * t⁻¹ with hz
  have hzZ : z ∈ Subgroup.zpowers s := hgt
  have hsz : Commute s z := by
    have hle : Subgroup.zpowers s ≤ Subgroup.centralizer ({s} : Set T) :=
      Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (Commute.refl s))
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hzZ)).symm
  have hdecomp : g * t * g⁻¹ = z * t := by rw [hz]; group
  have hconj := CFSG.RankThree.Classical2.liftComm_conj hφ hker hst g
  rw [hgs, hdecomp] at hconj
  have h1 : CFSG.RankThree.Classical2.liftComm φ hφ s z = 1 :=
    liftComm_eq_one_of_mem_zpowers hφ hker hzZ
  have hzt : Commute z t := by
    have hle : Subgroup.zpowers s ≤ Subgroup.centralizer ({t} : Set T) :=
      Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hst)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hzZ)
  have h1' : CFSG.RankThree.Classical2.liftComm φ hφ s⁻¹ z = 1 := by
    rw [CFSG.RankThree.Classical2.liftComm_inv_left hφ hker hsz, h1, inv_one]
  have h2 : CFSG.RankThree.Classical2.liftComm φ hφ s⁻¹ (z * t) = c⁻¹ := by
    rw [hzt.eq,
      CFSG.RankThree.Classical2.liftComm_mul_right (s := s⁻¹) (t := t) (t' := z) hφ hker
        hsz.inv_left,
      CFSG.RankThree.Classical2.liftComm_inv_left hφ hker hst, h1', mul_one, hc]
  have hcc : c = c⁻¹ := by
    calc c = CFSG.RankThree.Classical2.liftComm φ hφ s t := hc
      _ = CFSG.RankThree.Classical2.liftComm φ hφ s⁻¹ (z * t) := hconj.symm
      _ = c⁻¹ := h2
  have h2sq : c ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hcc]
    exact mul_inv_cancel c
  have hcpow : c ^ p = 1 := by
    have h := CFSG.RankThree.Classical2.liftComm_pow_left hφ hker hst p
    rw [hsp, CFSG.RankThree.Classical2.liftComm_one_left hφ hker] at h
    exact h.symm
  exact CFSG.RankThree.Classical2.eq_one_of_sq_eq_one_of_pow_eq_one hodd h2sq hcpow

theorem comap_closure_comm_of_cross {p k : ℕ} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) (hp : p.Prime) (hp2 : p ≠ 2) {h w : Fin k → T}
    (hcomm : ∀ i j, Commute (h i) (h j)) (hpow : ∀ i, h i ^ p = 1)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hcross : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ * (h j)⁻¹ ∈ Subgroup.zpowers (h i)) :
    ∀ x ∈ (Subgroup.closure (Set.range h)).comap φ,
      ∀ y ∈ (Subgroup.closure (Set.range h)).comap φ, x * y = y * x := by
  have hS : ∀ s ∈ Set.range h, ∀ t ∈ Set.range h, Commute s t := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hcomm i j
  refine CFSG.RankThree.CentralCover.comap_closure_comm hφ hker hS ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  by_cases hij : i = j
  · subst hij
    exact CFSG.RankThree.Classical2.liftComm_self hφ (h i)
  · exact liftComm_eq_one_of_conj_inv_of_mem_zpowers hφ hker hp hp2 (hcomm i j) (hpow i)
      (hinv i) (hcross i j hij)

end Pairing

section Lift

variable {Y T : Type*} [Group Y] [Group T] {φ : Y →* T}

theorem exists_lift_pow_eq_one (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {h w : T}
    (hpow : h ^ p = 1) (hinv : w * h * w⁻¹ = h⁻¹) : ∃ y : Y, φ y = h ∧ y ^ p = 1 := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  obtain ⟨y, hy⟩ := hφ h
  obtain ⟨g, hg⟩ := hφ w
  have hyp : y ^ p ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hy, hpow]
  have hyc : y ^ p ∈ Subgroup.center Y := hker hyp
  set c : Y := g * y * g⁻¹ * y with hc
  have hcker : c ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul, map_inv, hg, hy, hinv,
      inv_mul_cancel]
  have hcc : c ∈ Subgroup.center Y := hker hcker
  have hconj : g * y * g⁻¹ = c * y⁻¹ := by rw [hc]; group
  have h1 : g * y ^ p * g⁻¹ = y ^ p := by
    have h := Subgroup.mem_center_iff.1 hyc g
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : g * y ^ p * g⁻¹ = c ^ p * (y ^ p)⁻¹ := by
    have e : g * y ^ p * g⁻¹ = (g * y * g⁻¹) ^ p := conj_pow.symm
    rw [e, hconj]
    have hcomm : Commute c (y⁻¹) := ((Subgroup.mem_center_iff.1 hcc (y⁻¹)).symm :)
    rw [hcomm.mul_pow, inv_pow]
  rw [h1] at h2
  have hsq : (y ^ p) ^ 2 = c ^ p := by
    rw [pow_two]
    nth_rewrite 1 [h2]
    exact inv_mul_cancel_right _ _
  have hdecomp : ∀ a : Y, a ^ p = (a ^ 2) ^ m * a := by
    intro a
    rw [hm, pow_succ, pow_mul]
  have hpowpy : (y ^ p) ^ p = c ^ (p * m) * y ^ p := by
    rw [hdecomp (y ^ p), hsq, ← pow_mul]
  set u : Y := (c ^ m)⁻¹ * y ^ p with hu
  have huc : u ∈ Subgroup.center Y :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hcc m)) hyc
  have hupow : u ^ p = y ^ p := by
    have hcomm : Commute ((c ^ m)⁻¹) (y ^ p) := by
      have h1 : c ^ m ∈ Subgroup.center Y := Subgroup.pow_mem _ hcc m
      exact (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ h1) (y ^ p)).symm
    rw [hu, hcomm.mul_pow, inv_pow, ← pow_mul, hpowpy]
    rw [show m * p = p * m by rw [Nat.mul_comm], inv_mul_cancel_left]
  have huker : u ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    have h1 : φ (c ^ m) = 1 := by rw [map_pow, MonoidHom.mem_ker.1 hcker, one_pow]
    have h2 : φ (y ^ p) = 1 := MonoidHom.mem_ker.1 hyp
    rw [hu, map_mul, map_inv, h1, h2, inv_one, mul_one]
  refine ⟨y * u⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, hy, MonoidHom.mem_ker.1 huker, inv_one, mul_one]
  · have hcomm : Commute y (u⁻¹) :=
      Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ huc) y
    rw [hcomm.mul_pow, inv_pow, hupow, mul_inv_cancel]

end Lift

section Rank

variable {K : Type*} [Group K]

theorem card_closure_le_pow_of_commuting {p k : ℕ} (hp : p.Prime) {y : Fin k → K}
    (hpow : ∀ i, y i ^ p = 1) (hcomm : ∀ i j, Commute (y i) (y j)) :
    Nat.card (Subgroup.closure (Set.range y)) ≤ p ^ k := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set E : Subgroup K := Subgroup.closure (Set.range y) with hE
  have hS : ∀ s ∈ Set.range y, ∀ t ∈ Set.range y, Commute s t := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hcomm i j
  have hEpow : ∀ x ∈ E, x ^ p = 1 :=
    fun x hx => CFSG.RankThree.CentralCover.pow_eq_one_of_mem_closure hS
      (by rintro _ ⟨i, rfl⟩; exact hpow i) hx
  have hrank : Group.rank E ≤ k := by
    have h := Subgroup.rank_closure_finite_le_nat_card (G := K) (Set.range y)
    have h2 : Nat.card (Set.range y) ≤ k := by
      calc Nat.card (Set.range y) ≤ Nat.card (Fin k) :=
            Nat.card_le_card_of_surjective
              (fun i : Fin k => (⟨y i, ⟨i, rfl⟩⟩ : Set.range y))
              (fun z => by
                obtain ⟨i, hi⟩ := z.2
                exact ⟨i, Subtype.ext hi⟩)
        _ = k := Nat.card_fin k
    have h3 : Group.rank (Subgroup.closure (Set.range y)) ≤ k := h.trans h2
    simpa [hE] using h3
  haveI hEc : IsMulCommutative E := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact (CFSG.RankThree.CentralCover.commute_of_mem_closure hS
      (show (a : K) ∈ Subgroup.closure (Set.range y) from a.2)
      (show (b : K) ∈ Subgroup.closure (Set.range y) from b.2)).eq
  let : CommGroup E := IsMulCommutative.instCommGroup
  have hdvd : Nat.card E ∣ p ^ Group.rank E :=
    card_dvd_exponent_pow_rank' (G := E) (n := p) (fun x => by
      exact Subtype.ext (by simpa using hEpow (x : K) x.2))
  have hcardle : Nat.card E ≤ p ^ Group.rank E := Nat.le_of_dvd (pow_pos hp.pos _) hdvd
  exact hcardle.trans (Nat.pow_le_pow_right hp.pos hrank)

end Rank

theorem central_lift_le_twoLocalPrimeRank {K R : Type} [Group K] [Finite K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {h w : Fin k → R} (hpow : ∀ i, h i ^ p = 1) (hcomm : ∀ i j, Commute (h i) (h j))
    (hind : Nat.card (Subgroup.closure (Set.range h)) = p ^ k)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hcross : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ * (h j)⁻¹ ∈ Subgroup.zpowers (h i))
    {X : Subgroup R} (hX1 : X ≠ ⊥) (hX2 : IsPGroup 2 X)
    (hNX : ∀ i, h i ∈ Subgroup.normalizer (X : Set R)) :
    k + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank p K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let φ : K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφ : Function.Surjective φ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hker : φ.ker = Subgroup.center K := by
    rw [show φ = θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
  have hkerle : φ.ker ≤ Subgroup.center K := hker.le
  set D : Subgroup R := Subgroup.closure (Set.range h) with hD
  have hDcard : Nat.card D = p ^ k := hind
  have hFcomm := comap_closure_comm_of_cross hφ hkerle hp hp2 hcomm hpow hinv hcross
  choose y hy using fun i => exists_lift_pow_eq_one hφ hkerle hp hp2 (hpow i) (hinv i)
  set E : Subgroup K := Subgroup.closure (Set.range y) with hE
  have hyE : ∀ i, y i ∈ E := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hEcomap : E ≤ D.comap φ := by
    rw [hE, hD]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_comap.2 (by
      rw [(hy i).1]
      exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hEcomm : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x :=
    fun x hx z hz => hFcomm x (hEcomap hx) z (hEcomap hz)
  have hEmap : E.map φ = D := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]; exact hEcomap
    · rw [hD]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨y i, hyE i, (hy i).1⟩
  have hEcard : Nat.card E = p ^ k := by
    refine le_antisymm ?_ ?_
    · rw [hE]
      refine card_closure_le_pow_of_commuting hp (fun i => (hy i).2) ?_
      intro i j
      exact hEcomm (y i) (hyE i) (y j) (hyE j)
    · have h := Subgroup.card_map_dvd (H := E) φ
      rw [hEmap, hDcard] at h
      exact Nat.le_of_dvd Nat.card_pos h
  let ψ : E →* D := (φ.comp E.subtype).codRestrict D (fun x => hEcomap x.2)
  have hψrange : ψ.range = ⊤ := by
    have hmap : Subgroup.map D.subtype ψ.range = D := by
      apply le_antisymm
      · rintro _ ⟨x, -, rfl⟩
        exact x.2
      · refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨i, rfl⟩
        refine ⟨ψ ⟨y i, hyE i⟩, ?_, ?_⟩
        · exact MonoidHom.mem_range.2 ⟨⟨y i, hyE i⟩, rfl⟩
        · exact (hy i).1
    have htop : Subgroup.map D.subtype ψ.range = Subgroup.map D.subtype (⊤ : Subgroup D) := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
      exact hmap
    exact Subgroup.map_injective D.subtype_injective htop
  have hEker : E ⊓ φ.ker = ⊥ := by
    have hcard := Subgroup.card_ker_mul_card_range ψ
    rw [hψrange, Subgroup.card_top, hDcard, hEcard] at hcard
    have hker1 : Nat.card ψ.ker = 1 := by
      have hpk : 0 < p ^ k := pow_pos hp.pos k
      have h1 : Nat.card ψ.ker * p ^ k = 1 * p ^ k := by rw [hcard, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hpk h1
    have hψker : ψ.ker = ⊥ := (Subgroup.eq_bot_iff_card ψ.ker).mpr hker1
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.1⟩ : E) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact MonoidHom.mem_ker.1 hx.2
    rw [hψker] at hx'
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.1 hx')
  obtain ⟨A, hAle, hAab, hAcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp (Subgroup.center K)
  have hEA : E ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxker : x ∈ E ⊓ φ.ker := by
      refine ⟨hx.1, ?_⟩
      rw [hker]
      exact hAle hx.2
    rw [hEker] at hxker
    exact Subgroup.mem_bot.1 hxker
  let W : Subgroup K := E ⊔ A
  have hkercomap : φ.ker ≤ D.comap φ := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact D.one_mem
  have hAle_comap : A ≤ D.comap φ := (hker ▸ hAle).trans hkercomap
  have hWcomap : W ≤ D.comap φ := sup_le hEcomap hAle_comap
  have hWcomm : ∀ x ∈ W, ∀ z ∈ W, x * z = z * x :=
    fun x hx z hz => hFcomm x (hWcomap hx) z (hWcomap hz)
  have hEpowval : ∀ x ∈ E, x ^ p = 1 := by
    intro x hx
    rw [hE] at hx
    exact CFSG.RankThree.CentralCover.pow_eq_one_of_mem_closure
      (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hEcomm (y i) (hyE i) (y j) (hyE j))
      (by rintro _ ⟨i, rfl⟩; exact (hy i).2) hx
  have hWpow : ∀ x ∈ W, x ^ p = 1 := by
    intro x hx
    rw [show W = Subgroup.closure ((E : Set K) ∪ (A : Set K)) from
      Subgroup.sup_eq_closure E A] at hx
    refine CFSG.RankThree.CentralCover.pow_eq_one_of_mem_closure ?_ ?_ hx
    · rintro s (hs | hs) t (ht | ht)
      · exact hEcomm s hs t ht
      · exact Subgroup.mem_center_iff.1 (hAle ht) s
      · exact (Subgroup.mem_center_iff.1 (hAle hs) t).symm
      · exact congrArg Subtype.val (hAab.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
    · rintro s (hs | hs)
      · exact hEpowval s hs
      · exact hAab.2 s hs
  have hWab : IsElemAbelian p W :=
    ⟨⟨⟨fun x z => Subtype.ext (hWcomm x x.2 z z.2)⟩⟩, fun x hx => hWpow x hx⟩
  have hWcard : Nat.card W =
      p ^ (k + CFSG.Open.pRank p (Subgroup.center K)) := by
    have hcomm : ∀ x ∈ E, ∀ z ∈ A, x * z = z * x := fun x _ z hz =>
      Subgroup.mem_center_iff.1 (hAle hz) x
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E A hcomm
    rw [hEA, Subgroup.card_bot, mul_one, hEcard, hAcard, ← pow_add] at hcard
    exact hcard
  have hDnorm : D ≤ Subgroup.normalizer (X : Set R) := by
    rw [hD]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact hNX i
  obtain ⟨P, hP1, hP2, hPN⟩ :=
    CFSG.RankThree.CentralCover.exists_two_subgroup_normalized_of_cover hφ hkerle hX1 hX2
      (S := E) (fun x hx u hu =>
        (Subgroup.le_normalizer_iff.1 hDnorm) (φ x) (Subgroup.mem_comap.1 (hEcomap hx)) u hu)
  have hAnorm : A ≤ Subgroup.normalizer (P : Set K) :=
    hAle.trans ((Subgroup.center_le_centralizer (P : Set K)).trans
      (Subgroup.centralizer_le_normalizer _))
  exact le_twoLocalPrimeRank_of_normalizer hp hP1 hP2 hWab hWcard (sup_le hPN hAnorm)

end CFSG.LocalAnalysis.GLTheoremA
