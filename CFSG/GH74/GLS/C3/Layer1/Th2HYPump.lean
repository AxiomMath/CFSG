module

public import CFSG.GH74.GLS.C3.Layer1.Th2PumpTerm
public import CFSG.GH74.GLS.C3.Layer1.Th2HYGrp

public section

namespace CFSG.GH74.GLS.Th2.HY

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

variable {G : Type} [Group G]

section Bar

variable [Finite G]

omit [Finite G] in
theorem le_normalizer_O {u : G} {X : Subgroup G} (hX : X ≤ centralizer ({u} : Set G)) :
    X ≤ normalizer ((pPrimeCoreOf 2 (centralizer ({u} : Set G)) : Subgroup G) : Set G) :=
  fun _ ha => TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (hX ha))

omit [Finite G] in
theorem sbar_mem_bar_iff {u g : G} (hg : g ∈ centralizer ({u} : Set G)) {X : Subgroup G}
    (hX : X ≤ centralizer ({u} : Set G)) :
    sbar g hg ∈ bar u X ↔ g ∈ X ⊔ pPrimeCoreOf 2 (centralizer ({u} : Set G)) := by
  rw [mem_sup_iff_mul_of_le_normalizer (le_normalizer_O hX)]
  constructor
  · rintro ⟨m, hm, hmeq⟩
    have hm' : (m : G) ∈ X := Subgroup.mem_subgroupOf.mp hm
    refine ⟨m, hm', (m : G)⁻¹ * g, ?_, by group⟩
    have h1 : (m⁻¹ * ⟨g, hg⟩ : ↥(centralizer ({u} : Set G))) ∈
        pPrimeCore 2 ↥(centralizer ({u} : Set G)) := by
      have h2 : (QuotientGroup.mk m : barQ ↥(centralizer ({u} : Set G))) =
          QuotientGroup.mk ⟨g, hg⟩ := hmeq
      exact QuotientGroup.eq.1 h2
    exact ⟨_, h1, rfl⟩
  · rintro ⟨a, ha, o, ho, rfl⟩
    have haC : a ∈ centralizer ({u} : Set G) := hX ha
    have hoC : o ∈ centralizer ({u} : Set G) := TwoThin.pPrimeCoreOf_le _ ho
    refine ⟨⟨a, haC⟩, Subgroup.mem_subgroupOf.mpr ha, ?_⟩
    have h3 : (QuotientGroup.mk (⟨a, haC⟩ : ↥(centralizer ({u} : Set G))) :
        barQ ↥(centralizer ({u} : Set G))) = QuotientGroup.mk ⟨a * o, hg⟩ := by
      rw [QuotientGroup.eq]
      obtain ⟨o', ho', hoo'⟩ := ho
      have : ((⟨a, haC⟩ : ↥(centralizer ({u} : Set G)))⁻¹ * ⟨a * o, hg⟩ :
          ↥(centralizer ({u} : Set G))) = o' := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have : (o' : G) = o := hoo'
        rw [this]; group
      rw [this]
      exact ho'
    exact h3

end Bar

section Pump

variable [Finite G]

theorem exists_pumpup_at {x y : G} {K T S : Subgroup G} (hG : C3Hyp G) (h : Th2Std x y K T S)
    {v : G} (hv : v ∈ CxK x K) (hvo : orderOf v = 2) : ∃ M : Subgroup G, PumpUpLT 2 x K v M := by
  have hterm : IsTwoTerminal x K := h.v2ss.isV2Triple.2.1
  have hR3 : 3 ≤ pRank 2 ↥(centralizer ({v} : Set G)) :=
    TwoThin.rankThreeCentralizers G hG.kproper.1 hG.kproper.2.1
      (by have := hG.pRank_eq_four; omega) v hvo
  exact TwoThin.exists_pumpup_of_involution h.orderOf_x hvo h.comp hv.1 hv.2 hterm.1 hR3

theorem agree (hr4 : pRank 2 G = 4) {x v : G} {K Λ M₁ M₂ : Subgroup G}
    (hKq : CFSG.IsQuasisimple (kBar K)) (hKcen : CenterlessBar K) (hv : orderOf v = 2)
    (hvK : v ∈ centralizerSection K (pPrimeCoreOf 2 K)) (hΛ : IsLam x v K Λ)
    (hM₁ : IsPCompIn 2 (centralizer ({v} : Set G)) M₁) (hΛM₁ : bar v Λ ≤ bar v M₁)
    (hM₂ : IsPCompIn 2 (centralizer ({v} : Set G)) M₂) (hcen₂ : CenterlessBar M₂) :
    bar v M₁ = bar v M₂ := by
  by_contra hne
  have hc₁ : CFSG.IsComponent (bar v M₁) := isComponent_bar hM₁
  have hc₂ : CFSG.IsComponent (bar v M₂) := isComponent_bar hM₂
  have hcomm : bar v M₁ ≤ Subgroup.centralizer ((bar v M₂ : Subgroup _) : Set _) :=
    PumpTerm.comp_le_centralizer_of_ne hc₁ hc₂ hne
  have hΛM : Λ ≤ K := hΛ.le.trans inf_le_left
  have hΛY : Λ ≤ centralizer ({v} : Set G) := hΛ.le.trans inf_le_right
  refine PumpTerm.false_of_commuting_cover hr4 hv hM₂ hcen₂ hKq hKcen hΛM hΛY hΛ.cover hvK
    (fun l hl => ?_)
  have hlY : l ∈ centralizer ({v} : Set G) := hΛY hl
  have hmem : sbar l hlY ∈ bar v Λ := ⟨⟨l, hlY⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hcl : l ∈ CxK v M₂ := mem_CxK_of_centralizes hM₂ hlY (fun w hw => by
    have := Subgroup.mem_centralizer_iff.1 (hcomm (hΛM₁ hmem)) w hw
    rw [← this]
    group)
  exact (Subgroup.mem_inf.1 hcl).2

theorem bar_lam_eq {x v : G} {K Λ M₁ : Subgroup G} (hΛ : IsLam x v K Λ)
    (hM₁ : IsPCompIn 2 (centralizer ({v} : Set G)) M₁) (hle : bar v Λ ≤ bar v M₁)
    (e : kBar M₁ ≃* kBar K) : bar v Λ = bar v M₁ := by
  obtain ⟨φ, hφs, -, -⟩ := TwoThin.exists_phi (hΛ.le.trans inf_le_left)
    (hΛ.le.trans inf_le_right) hΛ.cover
  obtain ⟨e1⟩ := kBar_equiv_bar hM₁
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  calc Nat.card ↥(bar v M₁) = Nat.card (kBar M₁) := (Nat.card_congr e1.toEquiv).symm
    _ = Nat.card (kBar K) := Nat.card_congr e.toEquiv
    _ ≤ Nat.card ↥(bar v Λ) := Nat.card_le_card_of_surjective φ hφs

end Pump

section Lift

variable [Finite G]

omit [Finite G] in
theorem exists_fixed_mem_coset_gen {K Q N' : Subgroup G} (hQ2 : IsPGroup 2 ↥Q)
    (hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ ∈ K) (hQN : ∀ q ∈ Q, ∀ o ∈ N', q * o * q⁻¹ ∈ N')
    (hKN : ∀ k ∈ K, ∀ o ∈ N', k * o * k⁻¹ ∈ N') (hNK : N' ≤ K) (hN : Odd (Nat.card ↥N'))
    {k : G} (hk : k ∈ K) (hQt : ∀ q ∈ Q, ⁅k, q⁆ ∈ N') :
    ∃ c ∈ K, (∀ q ∈ Q, c * q = q * c) ∧ k⁻¹ * c ∈ N' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Set G := {x | x ∈ K ∧ k⁻¹ * x ∈ N'}
  have hS : ∀ q ∈ Q, ∀ x ∈ S, q * x * q⁻¹ ∈ S := by
    intro q hq x hx
    obtain ⟨hxK, hxO⟩ := hx
    refine ⟨hQK q hq x hxK, ?_⟩
    have hw : (⁅k, q⁆)⁻¹ ∈ N' := N'.inv_mem (hQt q hq)
    have h1 := hKN k⁻¹ (K.inv_mem hk) _ hw
    have h2 := hQN q hq _ hxO
    have h3 := N'.mul_mem h1 h2
    convert h3 using 1
    simp only [commutatorElement_def]
    group
  let inst : MulAction ↥Q ↥S :=
    { smul := fun q x => ⟨(q : G) * x * (q : G)⁻¹, hS q q.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : ↥Q) : G) * x * ((1 : ↥Q) : G)⁻¹ = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        show ((a * b : ↥Q) : G) * x * ((a * b : ↥Q) : G)⁻¹ =
          (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc]) }
  have hcard : ¬ 2 ∣ Nat.card ↥S := by
    let e : ↥N' ≃ ↥S :=
      { toFun := fun o => ⟨k * o, K.mul_mem hk (hNK o.2), by simp⟩
        invFun := fun x => ⟨k⁻¹ * x, x.2.2⟩
        left_inv := fun o => Subtype.ext (by simp)
        right_inv := fun x => Subtype.ext (by simp) }
    rw [← Nat.card_congr e]
    exact fun hd => (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 hd)
  obtain ⟨⟨x, hxK, hxO⟩, hfix⟩ := hQ2.nonempty_fixed_point_of_prime_not_dvd_card ↥S hcard
  refine ⟨x, hxK, fun q hq => ?_, hxO⟩
  have h : q * x * q⁻¹ = x := congrArg Subtype.val (MulAction.mem_fixedPoints.1 hfix ⟨q, hq⟩)
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem lift_fixed {v t : G} {Λ V : Subgroup G} (hV2 : IsPGroup 2 ↥V)
    (hVΛ : ∀ q ∈ V, ∀ l ∈ Λ, q * l * q⁻¹ ∈ Λ)
    (hVv : ∀ q ∈ V, q * v = v * q) (htV : ∀ q ∈ V, t * q = q * t)
    (htv : t ∈ centralizer ({v} : Set G)) (hΛC : Λ ≤ centralizer ({v} : Set G))
    (ht : t ∈ Λ ⊔ pPrimeCoreOf 2 (centralizer ({v} : Set G))) :
    ∃ c ∈ Λ, (∀ q ∈ V, c * q = q * c) ∧
      c⁻¹ * t ∈ pPrimeCoreOf 2 (centralizer ({v} : Set G)) := by
  set O₁ : Subgroup G := pPrimeCoreOf 2 (centralizer ({v} : Set G)) with hO₁
  have hCO : ∀ g ∈ centralizer ({v} : Set G), ∀ o ∈ O₁, g * o * g⁻¹ ∈ O₁ := fun g hg o ho =>
    TwoThin.pPrimeCoreOf_normalized _ hg ho
  obtain ⟨l₀, hl₀, o₁, ho₁, htl⟩ := (mem_sup_iff_mul_of_le_normalizer (le_normalizer_O hΛC)).1 ht
  have hl₀t : l₀ = t * o₁⁻¹ := by rw [htl]; group
  have hqC : ∀ q ∈ V, q ∈ centralizer ({v} : Set G) := fun q hq =>
    mem_centralizer_singleton_iff.2 (hVv q hq)
  have hodd : Odd (Nat.card ↥(Λ ⊓ O₁)) :=
    (TwoThin.card_pPrimeCoreOf_odd _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hQt : ∀ q ∈ V, ⁅l₀, q⁆ ∈ Λ ⊓ O₁ := by
    intro q hq
    refine ⟨?_, ?_⟩
    · have h1 : ⁅l₀, q⁆ = l₀ * (q * l₀⁻¹ * q⁻¹) := by simp only [commutatorElement_def]; group
      rw [h1]
      exact Λ.mul_mem hl₀ (hVΛ q hq _ (Λ.inv_mem hl₀))
    · have hcomm : q⁻¹ * t⁻¹ = t⁻¹ * q⁻¹ := by
        have : Commute t q := htV q hq
        exact (this.inv_inv).eq.symm
      have e : ⁅l₀, q⁆ = t * (o₁⁻¹ * (q * o₁ * q⁻¹)) * t⁻¹ := by
        rw [hl₀t]
        simp only [commutatorElement_def, mul_inv_rev, inv_inv]
        calc t * o₁⁻¹ * q * (o₁ * t⁻¹) * q⁻¹ = t * o₁⁻¹ * q * o₁ * (t⁻¹ * q⁻¹) := by group
          _ = t * o₁⁻¹ * q * o₁ * (q⁻¹ * t⁻¹) := by rw [hcomm]
          _ = t * (o₁⁻¹ * (q * o₁ * q⁻¹)) * t⁻¹ := by group
      rw [e]
      exact hCO t htv _ (O₁.mul_mem (O₁.inv_mem ho₁) (hCO q (hqC q hq) o₁ ho₁))
  obtain ⟨c, hcΛ, hcV, hcN⟩ := exists_fixed_mem_coset_gen (K := Λ) (Q := V) (N' := Λ ⊓ O₁) hV2
    hVΛ (fun q hq o ho => ⟨hVΛ q hq o ho.1, hCO q (hqC q hq) o ho.2⟩)
    (fun k hk o ho => ⟨Λ.mul_mem (Λ.mul_mem hk ho.1) (Λ.inv_mem hk), hCO k (hΛC hk) o ho.2⟩)
    inf_le_left hodd hl₀ hQt
  refine ⟨c, hcΛ, hcV, ?_⟩
  have h1 : c⁻¹ * t = (l₀⁻¹ * c)⁻¹ * o₁ := by rw [htl]; group
  rw [h1]
  exact O₁.mul_mem (O₁.inv_mem hcN.2) ho₁

end Lift

section Main

theorem le_pPrimeCoreOf_of_norm {N X : Subgroup G} (hNX : N ≤ X)
    (hnorm : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hodd : Odd (Nat.card ↥N)) :
    N ≤ pPrimeCoreOf 2 X := by
  have hnormal : (N.subgroupOf X).Normal := ⟨fun a ha h => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hnorm (h : G) h.2 (a : G) ha⟩
  have hcop : Nat.Coprime 2 (Nat.card ↥(N.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
    exact Nat.coprime_two_left.2 hodd
  have hle : N.subgroupOf X ≤ pPrimeCore 2 ↥X := le_sSup ⟨hnormal, hcop⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hNX]
  exact Subgroup.map_mono hle

variable [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer (V : Subgroup G) :
    normalizer (V : Set G) ≤ normalizer ((centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  have key : ∀ m ∈ normalizer (V : Set G), ∀ c ∈ centralizer (V : Set G),
      m * c * m⁻¹ ∈ centralizer (V : Set G) := by
    intro m hm c hc
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : m⁻¹ * w * m ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hm) w).1 hw
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hc _ hw'
    calc w * (m * c * m⁻¹) = m * ((m⁻¹ * w * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * w * m)) * m⁻¹ := by rw [h1]
      _ = m * c * m⁻¹ * w := by group
  exact ⟨fun hc => key n hn c hc, fun hc => by
    have := key n⁻¹ (inv_mem hn) _ hc
    simpa [mul_assoc] using this⟩

theorem inf_centralizer_le_pPrimeCoreOf {v : G} {V : Subgroup G} (hv : v ∈ V) :
    pPrimeCoreOf 2 (centralizer ({v} : Set G)) ⊓ centralizer (V : Set G) ≤
      pPrimeCoreOf 2 (normalizer (V : Set G)) := by
  set C : Subgroup G := centralizer (V : Set G) with hC
  have hCv : C ≤ centralizer ({v} : Set G) := fun c hc => by
    rw [mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hc v hv).symm
  have hodd : Odd (Nat.card ↥(pPrimeCoreOf 2 (centralizer ({v} : Set G)) ⊓ C)) :=
    (TwoThin.card_pPrimeCoreOf_odd _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have h1 : pPrimeCoreOf 2 (centralizer ({v} : Set G)) ⊓ C ≤ pPrimeCoreOf 2 C :=
    le_pPrimeCoreOf_of_norm inf_le_right
      (fun c hc o ho => ⟨TwoThin.pPrimeCoreOf_normalized _ (hCv hc) ho.1, C.mul_mem (C.mul_mem hc ho.2) (C.inv_mem hc)⟩)
      hodd
  have h2 : pPrimeCoreOf 2 C ≤ pPrimeCoreOf 2 (normalizer (V : Set G)) :=
    le_pPrimeCoreOf_of_norm
      ((TwoThin.pPrimeCoreOf_le C).trans (Subgroup.centralizer_le_normalizer (V : Set G)))
      (fun n hn o ho =>
        (Subgroup.mem_normalizer_iff.1
          (TwoThin.mem_normalizer_pPrimeCoreOf (normalizer_le_normalizer_centralizer V hn)) o).1 ho)
      (TwoThin.card_pPrimeCoreOf_odd C)
  exact h1.trans h2

theorem lam_normalized {x v : G} {K Λ : Subgroup G} (hΛ : IsLam x v K Λ) {q : G}
    (hq : q ∈ CxK x K) (hqv : q * v = v * q) : ∀ a ∈ Λ, q * a * q⁻¹ ∈ Λ := by
  have hqY : q ∈ centralizer ({v} : Set G) := mem_centralizer_singleton_iff.2 hqv
  have hqX : q ∈ normalizer ((K ⊓ centralizer ({v} : Set G) : Subgroup G) : Set G) :=
    TwoThin.mem_normalizer_inf (Subgroup.mem_inf.1 hq).2.1 (Subgroup.le_normalizer hqY)
  intro a ha
  exact conj_mem_of_unique_isPCompIn hΛ.pc hΛ.uniq hqX ha

theorem lam_conj_le (hG : C3Hyp G) {x y : G} {K T S : Subgroup G} (h : Th2Std x y K T S)
    (hKq : CFSG.IsQuasisimple (kBar K)) (hKcen : CenterlessBar K)
    {V : Subgroup G} (hVQ : V ≤ T ⊓ CxK x K) (hVel : CFSG.IsElementaryAbelian 2 ↥V)
    (hVne : V ≠ ⊥) {n : G} (hn : n ∈ normalizer (V : Set G)) :
    (twoGen (K ⊓ centralizer (V : Set G))).map (MulAut.conj n).toMonoidHom ≤
      twoGen (K ⊓ centralizer (V : Set G)) ⊔ pPrimeCoreOf 2 (normalizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr4 := hG.pRank_eq_four
  have hterm : IsTwoTerminal x K := h.v2ss.isV2Triple.2.1
  obtain ⟨hVc, hVsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hVel
  have hV2 : IsPGroup 2 ↥V := CFSG.IsElementaryAbelian.isPGroup 2 ↥V
  obtain ⟨v₁, hv₁V, hv₁o⟩ : ∃ v ∈ V, orderOf v = 2 := by
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hVne
    refine ⟨v, hv, orderOf_eq_prime (by rw [sq]; exact hVsq v hv) ?_⟩
    intro h1
    exact hv1 (Subtype.ext h1)
  have hv₁Q : v₁ ∈ CxK x K := (hVQ hv₁V).2
  obtain ⟨Λ₁, hΛ₁⟩ := C3.Layer1.PumpCalc.exists_isLam hv₁o h.comp hv₁Q.2
  obtain ⟨M₁, hlt₁⟩ := exists_pumpup_at hG h hv₁Q hv₁o
  obtain ⟨hxM₁, ⟨e₁⟩⟩ := hterm.2.1 v₁ M₁ hlt₁
  have hM₁c : IsPCompIn 2 (centralizer ({v₁} : Set G)) M₁ := hlt₁.2.1.2.2
  have hΛM₁ : bar v₁ Λ₁ ≤ bar v₁ M₁ := bar_le_of_stable hlt₁ hΛ₁ hxM₁
  have hΛeq : bar v₁ Λ₁ = bar v₁ M₁ := bar_lam_eq hΛ₁ hM₁c hΛM₁ e₁
  set X : Subgroup G := K ⊓ centralizer (V : Set G) with hX
  set N : Subgroup G := normalizer (V : Set G) with hN
  rw [Subgroup.map_le_iff_le_comap]
  refine twoGen_le_of_forall (fun g hgX k hgk => ?_)
  have hgK : g ∈ K := (Subgroup.mem_inf.1 hgX).1
  have hgCV : g ∈ centralizer (V : Set G) := (Subgroup.mem_inf.1 hgX).2
  set v' : G := n⁻¹ * v₁ * n with hv'
  have hv'V : v' ∈ V := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) v₁).1 hv₁V
    simpa using this
  have hv'o : orderOf v' = 2 := by
    have := orderOf_conj' n⁻¹ v₁
    simpa using this.trans hv₁o
  have hv'Q : v' ∈ CxK x K := (hVQ hv'V).2
  obtain ⟨Λ', hΛ'⟩ := C3.Layer1.PumpCalc.exists_isLam hv'o h.comp hv'Q.2
  obtain ⟨M₂, hlt₂⟩ := exists_pumpup_at hG h hv'Q hv'o
  obtain ⟨hxM₂, ⟨e₂⟩⟩ := hterm.2.1 v' M₂ hlt₂
  have hM₂c : IsPCompIn 2 (centralizer ({v'} : Set G)) M₂ := hlt₂.2.1.2.2
  have hΛ'M₂ : bar v' Λ' ≤ bar v' M₂ := bar_le_of_stable hlt₂ hΛ' hxM₂
  have hgC' : g ∈ centralizer ({v'} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hgCV v' hv'V).symm
  have hgΛ' : g ∈ Λ' := hΛ'.twoElt g ⟨hgK, hgC'⟩ ⟨k, hgk⟩
  have hmem2 : sbar g hgC' ∈ bar v' M₂ := hΛ'M₂ ⟨⟨g, hgC'⟩, Subgroup.mem_subgroupOf.mpr hgΛ', rfl⟩
  have hg2 : g ∈ M₂ ⊔ pPrimeCoreOf 2 (centralizer ({v'} : Set G)) :=
    (sbar_mem_bar_iff hgC' hM₂c.1).1 hmem2
  have hcv : cmap n (centralizer ({v'} : Set G)) = centralizer ({v₁} : Set G) := by
    show (centralizer ({v'} : Set G)).map (MulAut.conj n).toMonoidHom = _
    rw [Stage1.Thm2.Recip.map_centralizer_singleton_conj, show n * v' * n⁻¹ = v₁ by rw [hv']; group]
  have hO : cmap n (pPrimeCoreOf 2 (centralizer ({v'} : Set G))) =
      pPrimeCoreOf 2 (centralizer ({v₁} : Set G)) := by
    rw [← pPrimeCoreOf_cmap, hcv]
  have ht2 : n * g * n⁻¹ ∈ cmap n M₂ ⊔ pPrimeCoreOf 2 (centralizer ({v₁} : Set G)) := by
    have h1 : n * g * n⁻¹ ∈ cmap n (M₂ ⊔ pPrimeCoreOf 2 (centralizer ({v'} : Set G))) :=
      mem_cmap.2 (by simpa [mul_assoc] using hg2)
    have e1 : cmap n (M₂ ⊔ pPrimeCoreOf 2 (centralizer ({v'} : Set G))) =
        cmap n M₂ ⊔ cmap n (pPrimeCoreOf 2 (centralizer ({v'} : Set G))) :=
      Subgroup.map_sup _ _ _
    rwa [e1, hO] at h1
  have hM₂n : IsPCompIn 2 (centralizer ({v₁} : Set G)) (cmap n M₂) := by
    have := isPCompIn_cmap hM₂c n
    rwa [hcv] at this
  have hcen₂ : CenterlessBar (cmap n M₂) :=
    centerlessBar_of_equiv (centerlessBar_of_equiv hKcen e₂) (nonempty_quot_cmap n M₂).some
  have hag : bar v₁ M₁ = bar v₁ (cmap n M₂) :=
    agree hr4 hKq hKcen hv₁o hv₁Q.2 hΛ₁ hM₁c hΛM₁ hM₂n hcen₂
  have htC : n * g * n⁻¹ ∈ centralizer ({v₁} : Set G) :=
    (sup_le hM₂n.1 (TwoThin.pPrimeCoreOf_le _)) ht2
  have hbar2 : sbar (n * g * n⁻¹) htC ∈ bar v₁ (cmap n M₂) := (sbar_mem_bar_iff htC hM₂n.1).2 ht2
  have hbar1 : sbar (n * g * n⁻¹) htC ∈ bar v₁ Λ₁ := by
    rw [hΛeq, hag]
    exact hbar2
  have hΛC : Λ₁ ≤ centralizer ({v₁} : Set G) := hΛ₁.le.trans inf_le_right
  have ht1 : n * g * n⁻¹ ∈ Λ₁ ⊔ pPrimeCoreOf 2 (centralizer ({v₁} : Set G)) :=
    (sbar_mem_bar_iff htC hΛC).1 hbar1
  have htV : ∀ q ∈ V, (n * g * n⁻¹) * q = q * (n * g * n⁻¹) := by
    intro q hq
    have hq' : n⁻¹ * q * n ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) q).1 hq
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hgCV _ hq'
    calc (n * g * n⁻¹) * q = n * (g * (n⁻¹ * q * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * q * n) * g) * n⁻¹ := by rw [← h1]
      _ = q * (n * g * n⁻¹) := by group
  obtain ⟨c, hcΛ, hcV, hcO⟩ := lift_fixed hV2
    (fun q hq a ha => lam_normalized hΛ₁ (hVQ hq).2 (hVc q hq v₁ hv₁V) a ha)
    (fun q hq => hVc q hq v₁ hv₁V) htV htC hΛC ht1
  have hcX : c ∈ X := ⟨(hΛ₁.le.trans inf_le_left) hcΛ,
    Subgroup.mem_centralizer_iff.2 (fun w hw => (hcV w hw).symm)⟩
  have hoV : c⁻¹ * (n * g * n⁻¹) ∈ centralizer (V : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 (fun w hw => ?_)
    have h1 := Subgroup.mem_centralizer_iff.1 (inv_mem hcX.2) w hw
    have h2 := htV w hw
    calc w * (c⁻¹ * (n * g * n⁻¹)) = (w * c⁻¹) * (n * g * n⁻¹) := by group
      _ = (c⁻¹ * w) * (n * g * n⁻¹) := by rw [h1]
      _ = c⁻¹ * (w * (n * g * n⁻¹)) := by group
      _ = c⁻¹ * ((n * g * n⁻¹) * w) := by rw [← h2]
      _ = (c⁻¹ * (n * g * n⁻¹)) * w := by group
  have hoN : c⁻¹ * (n * g * n⁻¹) ∈ pPrimeCoreOf 2 N :=
    inf_centralizer_le_pPrimeCoreOf hv₁V ⟨hcO, hoV⟩
  have hXN : X ≤ normalizer ((pPrimeCoreOf 2 N : Subgroup G) : Set G) := fun a ha =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer
      (Subgroup.centralizer_le_normalizer (V : Set G) ha.2))
  have htX : n * g * n⁻¹ ∈ X ⊔ pPrimeCoreOf 2 N := by
    have : n * g * n⁻¹ = c * (c⁻¹ * (n * g * n⁻¹)) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hcX hoN
  have hpow : (n * g * n⁻¹) ^ (2 ^ k) = 1 := by
    have := (MulAut.conj n).toMonoidHom.map_pow g (2 ^ k)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [← this, hgk]
    simp
  exact twoElt_mem_sup hXN (TwoThin.card_pPrimeCoreOf_odd N) htX hpow

end Main

end CFSG.GH74.GLS.Th2.HY
