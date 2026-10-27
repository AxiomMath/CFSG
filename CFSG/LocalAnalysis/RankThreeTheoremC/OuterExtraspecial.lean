module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSLAux
import CFSG.LocalAnalysis.AGLEmbedding.CentralAlphaOut
import CFSG.LocalAnalysis.AGLEmbedding.RankOneAutomizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding
open CFSG.PreuniquenessRankFour.Helpers

section Linear

variable {p : ℕ} [Fact p.Prime]

private theorem det_upper (t : ZMod p) :
    (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
  rw [Matrix.det_fin_two_of]
  ring

private theorem det_lower (t : ZMod p) :
    (!![1, 0; t, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
  rw [Matrix.det_fin_two_of]
  ring

theorem exists_statedSL_upper (t : ZMod p) :
    ∃ A ∈ StatedSL 2 (ZMod p), (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, t; 0, 1] :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, t; 0, 1] (by rw [det_upper]; exact one_ne_zero),
    Subgroup.subset_closure (show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 from
      det_upper t), rfl⟩

theorem exists_statedSL_lower (t : ZMod p) :
    ∃ A ∈ StatedSL 2 (ZMod p), (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; t, 1] :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; t, 1] (by rw [det_lower]; exact one_ne_zero),
    Subgroup.subset_closure (show (!![1, 0; t, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 from
      det_lower t), rfl⟩

theorem eq_bot_or_eq_top_of_forall_mulVec_mem (W : AddSubgroup (Fin 2 → ZMod p))
    (hW : ∀ A ∈ StatedSL 2 (ZMod p), ∀ w ∈ W,
      (A : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  have hU : ∀ t : ZMod p, ∀ w ∈ W, (![t * w 1, 0] : Fin 2 → ZMod p) ∈ W := by
    intro t w hw
    obtain ⟨A, hA, hAeq⟩ := exists_statedSL_upper (p := p) t
    have h := W.sub_mem (hW A hA w hw) hw
    convert h using 1
    rw [hAeq]
    ext i
    fin_cases i
    · simp [dotProduct, Fin.sum_univ_two]
      ring
    · simp [dotProduct, Fin.sum_univ_two]
  have hL : ∀ t : ZMod p, ∀ w ∈ W, (![0, t * w 0] : Fin 2 → ZMod p) ∈ W := by
    intro t w hw
    obtain ⟨A, hA, hAeq⟩ := exists_statedSL_lower (p := p) t
    have h := W.sub_mem (hW A hA w hw) hw
    convert h using 1
    rw [hAeq]
    ext i
    fin_cases i <;> simp [dotProduct, Fin.sum_univ_two]
  obtain ⟨⟨w, hwW⟩, hw0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hbot
  have hw0' : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hboth : (∀ s : ZMod p, (![s, 0] : Fin 2 → ZMod p) ∈ W) ∧
      ∀ s : ZMod p, (![0, s] : Fin 2 → ZMod p) ∈ W := by
    by_cases h1 : w 1 = 0
    · have h0 : w 0 ≠ 0 := by
        intro h0
        apply hw0'
        ext i
        fin_cases i <;> simp [h0, h1]
      have hs : ∀ s : ZMod p, (![0, s] : Fin 2 → ZMod p) ∈ W := by
        intro s
        have := hL (s * (w 0)⁻¹) w hwW
        rwa [mul_assoc, inv_mul_cancel₀ h0, mul_one] at this
      refine ⟨fun s => ?_, hs⟩
      simpa using hU s ![0, 1] (hs 1)
    · have hs : ∀ s : ZMod p, (![s, 0] : Fin 2 → ZMod p) ∈ W := by
        intro s
        have := hU (s * (w 1)⁻¹) w hwW
        rwa [mul_assoc, inv_mul_cancel₀ h1, mul_one] at this
      refine ⟨hs, fun s => ?_⟩
      simpa using hL s ![1, 0] (hs 1)
  rw [eq_top_iff]
  intro v _
  have hv : v = ![v 0, 0] + ![0, v 1] := by
    ext i
    fin_cases i <;> simp
  rw [hv]
  exact W.add_mem (hboth.1 _) (hboth.2 _)

end Linear

section Irreducible

variable {X : Type*} [Group X] {p : ℕ} [Fact p.Prime]

theorem inf_le_map_center_or_le_sup_of_normal {E L Y : Subgroup X} [Y.Normal]
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p))
    (hSL : StatedSL 2 (ZMod p) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set X))).map (centerQuotientAction E e)) :
    E ⊓ Y ≤ (Subgroup.center E).map E.subtype ∨
      E ≤ Y ⊔ (Subgroup.center E).map E.subtype := by
  let f : E →* Multiplicative (Fin 2 → ZMod p) :=
    (e : E ⧸ Subgroup.center E →* Multiplicative (Fin 2 → ZMod p)).comp
      (QuotientGroup.mk' (Subgroup.center E))
  have hf : ∀ u : E, f u = e (u : E ⧸ Subgroup.center E) := fun u => rfl
  let W : AddSubgroup (Fin 2 → ZMod p) :=
    { carrier := {w | ∃ u : E, (u : X) ∈ Y ∧ Multiplicative.toAdd (f u) = w}
      zero_mem' := ⟨1, Y.one_mem, by rw [map_one, toAdd_one]⟩
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        exact ⟨u * v, Y.mul_mem hu hv, by simp [map_mul]⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u⁻¹, Y.inv_mem hu, by rw [map_inv, toAdd_inv]; rfl⟩ }
  have hW : ∀ A ∈ StatedSL 2 (ZMod p), ∀ w ∈ W,
      (A : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ w ∈ W := by
    rintro A hA _ ⟨u, hu, rfl⟩
    obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.mp (hSL hA)
    have hv : (g : X) * u * (g : X)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp g.2 u).mp u.2
    refine ⟨⟨_, hv⟩, ‹Y.Normal›.conj_mem _ hu _, ?_⟩
    exact (centerQuotientAction_mulVec E e g (v := ⟨_, hv⟩) rfl).symm
  rcases eq_bot_or_eq_top_of_forall_mulVec_mem W hW with hbot | htop
  · left
    intro x ⟨hxE, hxY⟩
    have h1 : Multiplicative.toAdd (f ⟨x, hxE⟩) ∈ W := ⟨⟨x, hxE⟩, hxY, rfl⟩
    rw [hbot, AddSubgroup.mem_bot] at h1
    have h2 : f ⟨x, hxE⟩ = 1 := Multiplicative.toAdd.injective h1
    rw [hf, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h2
    exact ⟨⟨x, hxE⟩, h2, rfl⟩
  · right
    intro x hx
    have h1 : Multiplicative.toAdd (f ⟨x, hx⟩) ∈ W := htop ▸ AddSubgroup.mem_top _
    obtain ⟨u, huY, hu⟩ := h1
    have h2 : f u = f ⟨x, hx⟩ := Multiplicative.toAdd.injective hu
    rw [hf, hf, e.injective.eq_iff, QuotientGroup.eq] at h2
    have hx' : x = (u : X) * ((u⁻¹ * ⟨x, hx⟩ : E) : X) := by simp
    rw [hx']
    exact Subgroup.mul_mem_sup huY ⟨_, h2, rfl⟩

end Irreducible

section Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem inf_sup_le_inf_sup_of_normal (P : Sylow p G) {K C : Subgroup G} [K.Normal] [C.Normal] :
    (P : Subgroup G) ⊓ (K ⊔ C) ≤ (P : Subgroup G) ⊓ K ⊔ C := by
  set S : Subgroup G := (P : Subgroup G) ⊓ (K ⊔ C) with hS
  set H : Subgroup G := (P : Subgroup G) ⊓ K ⊔ C with hH
  have hKH : K ⊔ H = K ⊔ C := by
    rw [hH, ← sup_assoc, sup_eq_left.mpr (inf_le_right : (P : Subgroup G) ⊓ K ≤ K)]
  have hcop : ¬ p ∣ H.relIndex (K ⊔ C) := by
    rw [← hKH, relIndex_sup_left_eq_of_normal]
    intro h
    refine not_dvd_relIndex_sylow_of_normal P K ?_
    rw [← Subgroup.inf_relIndex_right]
    exact h.trans (Subgroup.relIndex_dvd_of_le_left K le_sup_left)
  have hHS : H ≤ S ⊔ C :=
    sup_le_sup_right (le_inf inf_le_left (inf_le_right.trans le_sup_left)) C
  have hSKC : S ⊔ C ≤ K ⊔ C := sup_le inf_le_right le_sup_right
  have hdvd : H.relIndex (S ⊔ C) ∣ H.relIndex (K ⊔ C) :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex H _ _ hHS hSKC)
  have hpow : H.relIndex (S ⊔ C) ∣ Nat.card S := by
    refine (Subgroup.relIndex_dvd_of_le_left _ (le_sup_right : C ≤ H)).trans ?_
    rw [Subgroup.relIndex_sup_right]
    exact Subgroup.relIndex_dvd_card C S
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (P.isPGroup'.to_inf_left (K := K ⊔ C))
  rw [hn, Nat.dvd_prime_pow Fact.out] at hpow
  obtain ⟨j, -, hj⟩ := hpow
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hdvd
    exact hcop ((dvd_pow_self p hj0).trans hdvd)
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact le_sup_left.trans hj

theorem exists_mul_eq_of_mem_inf_sup (P : Sylow p G) {K C : Subgroup G} [K.Normal] [C.Normal]
    {r : G} (hrP : r ∈ (P : Subgroup G)) (hrKC : r ∈ K ⊔ C) :
    ∃ t ∈ (P : Subgroup G) ⊓ K, ∃ c ∈ (P : Subgroup G) ⊓ C, t * c = r := by
  have h : r ∈ ((P : Subgroup G) ⊓ K ⊔ C : Subgroup G) :=
    inf_sup_le_inf_sup_of_normal P ⟨hrP, hrKC⟩
  rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at h
  obtain ⟨t, ht, c, hc, rfl⟩ := h
  refine ⟨t, ht, c, ⟨?_, hc⟩, rfl⟩
  have h' := (P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem ht.1) hrP
  rwa [inv_mul_cancel_left] at h'

theorem exists_conj_mem_sylow_of_isPGroup (S : Sylow p G) {Q : Subgroup G} (hQ : IsPGroup p Q) :
    ∃ g : G, ∀ q ∈ Q, g⁻¹ * q * g ∈ (S : Subgroup G) := by
  obtain ⟨T, hQT⟩ := hQ.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S T
  refine ⟨g, fun q hq => ?_⟩
  have h := hQT hq
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
  simpa [MulAut.smul_def, mul_assoc] using h

theorem inf_normal_ne_bot_of_dvd_card (P : Sylow p G) {K : Subgroup G} [K.Normal]
    (hKp : p ∣ Nat.card K) : (P : Subgroup G) ⊓ K ≠ ⊥ := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hKp
  have hxp : IsPGroup p (Subgroup.zpowers (x : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one]
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow_of_isPGroup P hxp
  have hxg := hg x (Subgroup.mem_zpowers _)
  intro hbot
  have hK : g⁻¹ * (x : G) * g ∈ K := by
    simpa using ‹K.Normal›.conj_mem (x : G) x.2 g⁻¹
  have h1 : g⁻¹ * (x : G) * g ∈ (P : Subgroup G) ⊓ K := ⟨hxg, hK⟩
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : (x : G) = 1 := by
    have := congrArg (fun y => g * y * g⁻¹) h1
    simpa [mul_assoc] using this
  have hx1 : x = 1 := Subtype.ext h2
  rw [hx1, orderOf_one] at hx
  exact (Fact.out : p.Prime).one_lt.ne hx

end Sylow

theorem exists_orderOf_eq_prime_commute {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {R S : Subgroup X} (hR : IsPGroup p R) (hSR : S ≤ R)
    (hSn : R ≤ Subgroup.normalizer (S : Set X)) (hS : S ≠ ⊥) :
    ∃ w ∈ S, orderOf w = p ∧ ∀ r ∈ R, Commute r w := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hn : (S.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSR).mpr hSn
  have hne : S.subgroupOf R ≠ ⊥ := by
    intro hbot
    apply hS
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hSR ha⟩ : R) ∈ S.subgroupOf R := Subgroup.mem_subgroupOf.mpr ha
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hB := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hBp : IsPGroup p (S.subgroupOf R ⊓ Subgroup.center R : Subgroup R) :=
    hR.to_subgroup _
  have hdvd : p ∣ Nat.card (S.subgroupOf R ⊓ Subgroup.center R : Subgroup R) :=
    hBp.card_eq_or_dvd.resolve_left fun h => hB (Subgroup.card_eq_one.mp h)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨((x : R) : X), Subgroup.mem_subgroupOf.mp x.2.1, ?_, fun r hr => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · have h := Subgroup.mem_center_iff.mp x.2.2 ⟨r, hr⟩
    exact congrArg Subtype.val h

theorem le_normalizer_inf_of_normal_right {X : Type*} [Group X] (R K : Subgroup X) [K.Normal] :
    R ≤ Subgroup.normalizer ((R ⊓ K : Subgroup X) : Set X) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨hhR, hhK⟩
    exact ⟨R.mul_mem (R.mul_mem hr hhR) (R.inv_mem hr), ‹K.Normal›.conj_mem _ hhK _⟩
  · rintro ⟨hhR, hhK⟩
    have hh : h = r⁻¹ * (r * h * r⁻¹) * r := by group
    rw [hh]
    refine ⟨R.mul_mem (R.mul_mem (R.inv_mem hr) hhR) hr, ?_⟩
    have := ‹K.Normal›.conj_mem _ hhK r⁻¹
    rwa [inv_inv] at this

section Main

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

omit [Finite X] in
theorem commutator_mem_center_of_mulEquiv {E : Type*} [Group E]
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)) (u v : E) :
    (v * u)⁻¹ * (u * v) ∈ Subgroup.center E := by
  rw [← QuotientGroup.eq]
  apply e.injective
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul, mul_comm]

omit [Finite X] in
theorem not_forall_mul_comm_of_mulEquiv {E : Type*} [Group E]
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)) :
    ¬ ∀ u v : E, u * v = v * u := by
  intro hcomm
  have htop : Subgroup.center E = ⊤ :=
    (Subgroup.eq_top_iff' _).mpr fun x => Subgroup.mem_center_iff.mpr fun g => hcomm g x
  have hsub : Subsingleton (E ⧸ Subgroup.center E) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  have hsub' : Subsingleton (Multiplicative (Fin 2 → ZMod p)) := e.surjective.subsingleton
  have h01 : (Multiplicative.ofAdd (![1, 0] : Fin 2 → ZMod p)) =
      Multiplicative.ofAdd (![0, 0] : Fin 2 → ZMod p) := Subsingleton.elim _ _
  have h02 := congrFun (Multiplicative.ofAdd.injective h01) 0
  simp at h02

omit [Fact p.Prime] in
theorem inf_centralizer_eq_center_map_of_isCyclic' {R E K : Subgroup X} {z : X}
    (hER : E ≤ R) (hEp : ∀ e ∈ E, e ^ p = 1)
    (hZE : (Subgroup.center E).map E.subtype = Subgroup.zpowers z)
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p)
    (hcyc : IsCyclic (R ⊓ Subgroup.centralizer (K : Set X) : Subgroup X)) :
    E ⊓ Subgroup.centralizer (K : Set X) = (Subgroup.center E).map E.subtype := by
  have hzZ : z ∈ (Subgroup.center E).map E.subtype := by
    rw [hZE]
    exact Subgroup.mem_zpowers z
  have hle : Subgroup.zpowers z ≤ E ⊓ Subgroup.centralizer (K : Set X) :=
    Subgroup.zpowers_le.mpr ⟨Subgroup.map_subtype_le _ hzZ, Subgroup.center_le_centralizer _ hz⟩
  have hcycE : IsCyclic (E ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) :=
    Subgroup.isCyclic_of_le (inf_le_inf_right _ hER)
  rw [hZE]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, hzp]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard
    (α := (E ⊓ Subgroup.centralizer (K : Set X) : Subgroup X))
  rw [← hg]
  exact Nat.le_of_dvd (hzp ▸ orderOf_pos z) (orderOf_dvd_of_pow_eq_one
    (Subtype.ext (by simpa using hEp g g.2.1)))

theorem inf_sup_centralizer_le_center_map (R : Sylow p X) {K : Subgroup X} [K.Normal]
    (hK1 : Subgroup.center K = ⊥) {z : X} (hz : z ∈ Subgroup.center X)
    (hcyc : IsCyclic ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X) : Subgroup X))
    {E L : Subgroup X} (hER : E ≤ (R : Subgroup X))
    (hEZ : (Subgroup.center E).map E.subtype = Subgroup.zpowers z)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p))
    (hSL : StatedSL 2 (ZMod p) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set X))).map (centerQuotientAction E e)) :
    E ⊓ (K ⊔ Subgroup.centralizer (K : Set X)) ≤ (Subgroup.center E).map E.subtype := by
  have hZC : (Subgroup.center E).map E.subtype ≤ Subgroup.centralizer (K : Set X) := by
    rw [hEZ]
    exact (Subgroup.zpowers_le.mpr hz).trans (Subgroup.center_le_centralizer _)
  have hKC : K ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
    rw [eq_bot_iff]
    intro k ⟨hkK, hkC⟩
    have hmem : (⟨k, hkK⟩ : K) ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hkC g g.2)
    rw [hK1, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
  rcases inf_le_map_center_or_le_sup_of_normal (Y := K ⊔ Subgroup.centralizer (K : Set X)) e hSL
    with h | h
  · exact h
  exfalso
  have hEY : E ≤ K ⊔ Subgroup.centralizer (K : Set X) :=
    h.trans (sup_le le_rfl (hZC.trans le_sup_right))
  refine not_forall_mul_comm_of_mulEquiv e fun u v => ?_
  obtain ⟨t₁, ht₁, c₁, hc₁, h₁⟩ := exists_mul_eq_of_mem_inf_sup R (hER u.2) (hEY u.2)
  obtain ⟨t₂, ht₂, c₂, hc₂, h₂⟩ := exists_mul_eq_of_mem_inf_sup R (hER v.2) (hEY v.2)
  have hζ := commutator_mem_center_of_mulEquiv e u v
  set ζ : X := (((v * u)⁻¹ * (u * v) : E) : X) with hζdef
  have hζz : ζ ∈ (Subgroup.center X : Set X) := by
    have : ζ ∈ Subgroup.zpowers z := hEZ ▸ ⟨_, hζ, rfl⟩
    exact Subgroup.zpowers_le.mpr hz this
  have hζcomm : ∀ g : X, g * ζ = ζ * g := fun g => Subgroup.mem_center_iff.mp hζz g
  have hζC : ζ ∈ Subgroup.centralizer (K : Set X) := hZC ⟨_, hζ, rfl⟩
  have hcomm : c₁ * c₂ = c₂ * c₁ := by
    let _ : CommGroup ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) :=
      IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨c₁, hc₁⟩ : ↥((R : Subgroup X) ⊓
      Subgroup.centralizer (K : Set X))) ⟨c₂, hc₂⟩)
  have hc₁t₂ : c₁ * t₂ = t₂ * c₁ := (Subgroup.mem_centralizer_iff.mp hc₁.2 t₂ ht₂.2).symm
  have hc₂t₁ : c₂ * t₁ = t₁ * c₂ := (Subgroup.mem_centralizer_iff.mp hc₂.2 t₁ ht₁.2).symm
  have huv : (u : X) * v = (v : X) * u * ζ := by
    rw [hζdef]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have key : t₁ * t₂ = t₂ * t₁ * ζ := by
    have h3 : t₁ * t₂ * (c₁ * c₂) = t₂ * t₁ * ζ * (c₁ * c₂) := by
      calc t₁ * t₂ * (c₁ * c₂) = t₁ * (c₁ * t₂) * c₂ := by rw [hc₁t₂]; group
        _ = (t₁ * c₁) * (t₂ * c₂) := by group
        _ = (u : X) * v := by rw [h₁, h₂]
        _ = (v : X) * u * ζ := huv
        _ = (t₂ * c₂) * (t₁ * c₁) * ζ := by rw [h₁, h₂]
        _ = t₂ * (c₂ * t₁) * c₁ * ζ := by group
        _ = t₂ * t₁ * (c₂ * c₁) * ζ := by rw [hc₂t₁]; group
        _ = t₂ * t₁ * (c₁ * c₂) * ζ := by rw [hcomm]
        _ = t₂ * t₁ * ζ * (c₁ * c₂) := by rw [mul_assoc (t₂ * t₁), hζcomm (c₁ * c₂), ← mul_assoc]
    exact mul_right_cancel h3
  have hζK : ζ ∈ K := by
    have : ζ = (t₂ * t₁)⁻¹ * (t₁ * t₂) := by
      rw [key]
      group
    rw [this]
    exact K.mul_mem (K.inv_mem (K.mul_mem ht₂.2 ht₁.2)) (K.mul_mem ht₁.2 ht₂.2)
  have hζ1 : ζ = 1 := by
    have : ζ ∈ K ⊓ Subgroup.centralizer (K : Set X) := ⟨hζK, hζC⟩
    rw [hKC, Subgroup.mem_bot] at this
    exact this
  rw [hζ1, mul_one] at huv
  exact Subtype.ext huv

theorem three_le_pRank_mulAut_of_outer_extraspecial (R : Sylow p X) {K : Subgroup X} [K.Normal]
    (hK1 : Subgroup.center K = ⊥) (hKp : p ∣ Nat.card K) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p)
    (hcyc : IsCyclic ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X) : Subgroup X))
    {E L : Subgroup X} (hER : E ≤ (R : Subgroup X)) (hEcard : Nat.card E = p ^ 3)
    (hEexp : ∀ x ∈ E, x ^ p = 1) (hEZ : (Subgroup.center E).map E.subtype = Subgroup.zpowers z)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p))
    (hSL : StatedSL 2 (ZMod p) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set X))).map (centerQuotientAction E e)) :
    3 ≤ Open.pRank p (⊤ : Subgroup (MulAut K)) := by
  have hp := (Fact.out : p.Prime)
  have hEC := inf_centralizer_eq_center_map_of_isCyclic' hER hEexp hEZ hz hzp hcyc
  have hEY := inf_sup_centralizer_le_center_map R hK1 hz hcyc hER hEZ e hSL
  set ρ : X →* MulAut K := MulAut.conjNormal (H := K) with hρ
  set A : Subgroup (MulAut K) := E.map ρ with hA
  have hAel : IsElemAbelian p A := isElemAbelian_map_conjNormal hEexp hEC e
  have hAcard : Nat.card A = p ^ 2 := card_map_conjNormal hEcard hEC e
  have hS : (R : Subgroup X) ⊓ K ≠ ⊥ := inf_normal_ne_bot_of_dvd_card R hKp
  have hSn := le_normalizer_inf_of_normal_right (R : Subgroup X) K
  obtain ⟨w, ⟨hwR, hwK⟩, hwp, hwc⟩ :=
    exists_orderOf_eq_prime_commute R.isPGroup' inf_le_left hSn hS
  set y : MulAut K := ρ w with hy
  have hyp : y ^ p = 1 := by
    have : w ^ p = 1 := hwp ▸ pow_orderOf_eq_one w
    rw [hy, ← map_pow, this, map_one]
  have hyC : y ∈ Subgroup.centralizer (A : Set (MulAut K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨e₀, he₀, rfl⟩
    rw [hy, ← map_mul, ← map_mul, (hwc e₀ (hER he₀)).eq]
  have hyA : y ∉ A := by
    rintro ⟨e₀, he₀, hρe⟩
    have hker : w⁻¹ * e₀ ∈ Subgroup.centralizer (K : Set X) := by
      rw [← ker_conjNormal_eq_centralizer K, MonoidHom.mem_ker, map_mul, map_inv, hρe, hy]
      exact inv_mul_cancel _
    have hmem : e₀ ∈ K ⊔ Subgroup.centralizer (K : Set X) := by
      have := Subgroup.mul_mem_sup hwK hker
      simpa using this
    have hC : e₀ ∈ Subgroup.centralizer (K : Set X) := by
      have := hEY ⟨he₀, hmem⟩
      rw [← hEC] at this
      exact this.2
    have hρ1 : ρ e₀ = 1 := by
      rw [← MonoidHom.mem_ker, hρ, ker_conjNormal_eq_centralizer]
      exact hC
    have hwC : w ∈ Subgroup.centralizer (K : Set X) := by
      rw [← ker_conjNormal_eq_centralizer K, MonoidHom.mem_ker]
      exact hy.symm.trans (hρe ▸ hρ1)
    have hmem' : (⟨w, hwK⟩ : K) ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hwC g g.2)
    rw [hK1, Subgroup.mem_bot] at hmem'
    have hw1 : w = 1 := congrArg Subtype.val hmem'
    rw [hw1, orderOf_one] at hwp
    exact hp.one_lt.ne hwp
  have hE := isElemAbelian_sup_zpowers_of_mem_centralizer hAel hyC hyp
  have hlt : A < A ⊔ Subgroup.zpowers y := lt_of_le_of_ne le_sup_left fun h =>
    hyA (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hPG : IsPGroup p (A ⊔ Subgroup.zpowers y : Subgroup (MulAut K)) :=
    fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hPG
  have hcard := Subgroup.card_lt_of_lt hlt
  rw [hAcard, hm, pow_lt_pow_iff_right₀ hp.one_lt] at hcard
  exact (show 3 ≤ m by omega).trans
    (le_csSup (pRank_bddAbove p hp _) ⟨_, le_top, hE, hm⟩)

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC
