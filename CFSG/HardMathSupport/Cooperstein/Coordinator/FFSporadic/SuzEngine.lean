module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OuterBound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.HyperplaneCover
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

section Generation

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {S : Type} [Group S]

@[expose] noncomputable def psiN (L : Subgroup (MulAut W)) (e : CQ L ≃* S) :
    ↥(Subgroup.normalizer (L : Set (MulAut W))) →* MulAut S where
  toFun b := psiAut L e b.2
  map_one' := psiAut_one e _
  map_mul' b b' := psiAut_mul e b.2 b'.2 _

theorem psiN_of_mem (e : CQ L ≃* S) (l : ↥L) :
    psiN L e ⟨(l : MulAut W), Subgroup.le_normalizer l.2⟩ =
      MulAut.conj (e (QuotientGroup.mk l)) := by
  ext s
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm s)
  have hs : s = e (QuotientGroup.mk y) := by rw [hy]; simp
  rw [hs]
  show psiAut L e _ (e (QuotientGroup.mk y)) = _
  rw [psiAut_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 2

theorem commutes_of_psiAut_eq_one (hperf : Group.IsPerfect ↥L) (e : CQ L ≃* S)
    {c : MulAut W} (hc : c ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (h : psiAut L e hc = 1) : ∀ x ∈ L, x * c = c * x := by
  have hcentral : ∀ x : ↥L, x⁻¹ * conjAut L hc x ∈ Subgroup.center ↥L := by
    intro x
    rw [← QuotientGroup.eq]
    apply e.injective
    have h1 := psiAut_mk e hc x
    rw [h, MulAut.one_apply] at h1
    exact h1
  let f : ↥L →* ↥(Subgroup.center ↥L) :=
    MonoidHom.mk' (fun x => ⟨x⁻¹ * conjAut L hc x, hcentral x⟩) (by
      intro x y
      apply Subtype.ext
      have hz := Subgroup.mem_center_iff.1 (hcentral x) y⁻¹
      show (x * y)⁻¹ * conjAut L hc (x * y) = (x⁻¹ * conjAut L hc x) * (y⁻¹ * conjAut L hc y)
      calc (x * y)⁻¹ * conjAut L hc (x * y)
          = y⁻¹ * (x⁻¹ * conjAut L hc x) * conjAut L hc y := by
            rw [map_mul]; group
        _ = (x⁻¹ * conjAut L hc x) * y⁻¹ * conjAut L hc y := by rw [hz]
        _ = (x⁻¹ * conjAut L hc x) * (y⁻¹ * conjAut L hc y) := by group)
  have hfker : (⊤ : Subgroup ↥L) ≤ f.ker := by
    rw [← hperf.commutator_eq_top, commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext (Subgroup.mem_center_iff.1 (f g₁).2 (f g₂)).symm)
  intro x hx
  have h1 := f.mem_ker.1 (hfker (Subgroup.mem_top ⟨x, hx⟩))
  have h2 := congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : MulAut W)) h1
  simp only [Subgroup.coe_one] at h2
  have h3 : (x : MulAut W)⁻¹ * (c * x * c⁻¹) = 1 := h2
  have h5 : c * x * c⁻¹ = x := (inv_mul_eq_one.1 h3).symm
  calc x * c = (c * x * c⁻¹) * c := by rw [h5]
    _ = c * x := by group

variable [Finite W]

theorem card_le_index_pow_of_psi_generation (hW : ∀ w : W, w * w = 1)
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L) (hL : L ≠ ⊥) {E : Subgroup (MulAut W)}
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    (e : CQ L ≃* S) {b : MulAut W} (hbE : b ∈ E) (cs : List S)
    (hgen : (MulAut.conj : S →* MulAut S).range ≤ Subgroup.closure
      {x : MulAut S | ∃ c ∈ cs, x = MulAut.conj c * psiAut L e (hE hbE) * (MulAut.conj c)⁻¹}) :
    Nat.card W ≤ (fixV (Subgroup.zpowers b)).index ^ cs.length := by
  classical
  set N : Subgroup (MulAut W) := Subgroup.normalizer (L : Set (MulAut W)) with hN
  let π : ↥L →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥L := by
    ext x
    simp [π]
  obtain ⟨ls, hls⟩ := (List.map_surjective_iff.2 hπ) cs
  have hlen : ls.length = cs.length := by rw [← hls, List.length_map]
  let bN : ↥N := ⟨b, hE hbE⟩
  let cN : ↥L → ↥N := fun l => ⟨(l : MulAut W), Subgroup.le_normalizer l.2⟩
  let gens : Set ↥N := {x | ∃ l ∈ ls, x = cN l * bN * (cN l)⁻¹}
  let K' : Subgroup ↥N := Subgroup.closure gens
  have hK'LE : K' ≤ (L ⊔ E).comap N.subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, -, rfl⟩
    show (l : MulAut W) * b * (l : MulAut W)⁻¹ ∈ L ⊔ E
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left l.2)
      (Subgroup.mem_sup_right hbE)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left l.2))
  have hρK : (MulAut.conj : S →* MulAut S).range ≤ K'.map (psiN L e) := by
    refine hgen.trans ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    rw [← hls] at hc
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hc
    refine ⟨cN l * bN * (cN l)⁻¹, Subgroup.subset_closure ⟨l, hl, rfl⟩, ?_⟩
    have hcl : psiN L e (cN l) = MulAut.conj (π l) := psiN_of_mem e l
    rw [map_mul, map_mul, map_inv, hcl]
    rfl
  let J : Subgroup ↥L := (K'.map N.subtype).comap L.subtype
  have hJ : ∀ s : S, ∃ x ∈ J, π x = s := by
    intro s
    obtain ⟨x, hxK, hxs⟩ := hρK ⟨s, rfl⟩
    obtain ⟨l, hl⟩ := hπ s
    have hxN : (x : MulAut W) ∈ N := x.2
    set y : ↥N := (cN l)⁻¹ * x with hy
    have hψy : psiN L e y = 1 := by
      have hcl : psiN L e (cN l) = MulAut.conj (π l) := psiN_of_mem e l
      rw [hy, map_mul, map_inv, hcl, hxs, hl]
      simp
    have hycomm : ∀ z ∈ L, z * (y : MulAut W) = (y : MulAut W) * z :=
      commutes_of_psiAut_eq_one hperf e y.2 hψy
    have hyLE : (y : MulAut W) ∈ L ⊔ E := by
      have h1 : (x : MulAut W) ∈ L ⊔ E := hK'LE hxK
      have h2 : ((l : ↥L) : MulAut W)⁻¹ ∈ L ⊔ E := Subgroup.inv_mem _ (Subgroup.mem_sup_left l.2)
      exact Subgroup.mul_mem _ h2 h1
    have hyL : (y : MulAut W) ∈ L :=
      centralizer_inf_le hW hirr hE hEel ⟨hyLE, Subgroup.mem_centralizer_iff.2 hycomm⟩
    have hxL : (x : MulAut W) ∈ L := by
      have : (x : MulAut W) = (l : MulAut W) * (y : MulAut W) := by
        rw [hy]
        show (x : MulAut W) = (l : MulAut W) * ((l : MulAut W)⁻¹ * (x : MulAut W))
        group
      rw [this]
      exact L.mul_mem l.2 hyL
    refine ⟨⟨(x : MulAut W), hxL⟩, ⟨x, hxK, rfl⟩, ?_⟩
    have hzc : (⟨(y : MulAut W), hyL⟩ : ↥L) ∈ Subgroup.center ↥L :=
      Subgroup.mem_center_iff.2 fun z => Subtype.ext (hycomm z z.2)
    have hxeq : (⟨(x : MulAut W), hxL⟩ : ↥L) = l * ⟨(y : MulAut W), hyL⟩ := by
      apply Subtype.ext
      show (x : MulAut W) = (l : MulAut W) * (y : MulAut W)
      rw [hy]
      show (x : MulAut W) = (l : MulAut W) * ((l : MulAut W)⁻¹ * (x : MulAut W))
      group
    rw [hxeq, map_mul, ← hl]
    have : π ⟨(y : MulAut W), hyL⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hzc
    rw [this, mul_one]
  have hJtop : J = ⊤ := by
    apply eq_top_of_sup_center_eq_top hperf
    rw [eq_top_iff]
    intro x _
    obtain ⟨s, hs⟩ : ∃ s, π x = s := ⟨_, rfl⟩
    obtain ⟨j, hj, hjs⟩ := hJ s
    have hxj : x⁻¹ * j ∈ Subgroup.center ↥L := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hs, hjs, inv_mul_cancel]
    have : x = j * (x⁻¹ * j)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem_sup hj (Subgroup.inv_mem _ hxj)
  have hLK : L ≤ Subgroup.closure {x : MulAut W | x ∈ ls.map
      (fun c : ↥L => (c : MulAut W) * b * (c : MulAut W)⁻¹)} := by
    intro x hx
    have hxJ : (⟨x, hx⟩ : ↥L) ∈ J := by rw [hJtop]; trivial
    obtain ⟨z, hz, hzx⟩ := hxJ
    have hzx' : (z : MulAut W) = x := hzx
    rw [← hzx']
    have : K'.map N.subtype ≤ Subgroup.closure {x : MulAut W | x ∈ ls.map
        (fun c : ↥L => (c : MulAut W) * b * (c : MulAut W)⁻¹)} := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨t, ⟨l, hl, rfl⟩, rfl⟩
      exact Subgroup.subset_closure (List.mem_map.2 ⟨l, hl, rfl⟩)
    exact this ⟨z, hz, rfl⟩
  set bs : List (MulAut W) := ls.map (fun c : ↥L => (c : MulAut W) * b * (c : MulAut W)⁻¹) with hbs
  have hfixK : fixV (Subgroup.closure {x : MulAut W | x ∈ bs}) = ⊥ := by
    rw [eq_bot_iff, ← fixV_eq_bot_of_irr hirr hL]
    exact CFSG.Quasithin.fixV_anti hLK
  have hidx : (fixV (Subgroup.closure {x : MulAut W | x ∈ bs})).index = Nat.card W := by
    rw [hfixK, Subgroup.index_bot]
  rw [← hidx]
  refine (index_fixV_closure_le bs).trans ?_
  have hrep : bs.map (fun x => (fixV (Subgroup.zpowers x)).index) =
      List.replicate cs.length (fixV (Subgroup.zpowers b)).index := by
    rw [hbs, List.map_map, ← hlen, List.map_eq_replicate_iff]
    intro x hx
    exact index_fixV_conj (x : MulAut W) b
  rw [hrep, List.prod_replicate]

end Generation

section Lower

theorem card_modEq_inf_of_conj {G : Type} [Group G] (r : ℕ) [Fact r.Prime] {u : G}
    (hu : u ^ r = 1) (R Z : Subgroup G) [Finite R] (hR : ∀ x ∈ R, u * x * u⁻¹ ∈ R)
    (hZu : ∀ z ∈ Z, u * z * u⁻¹ = z) (hfix : ∀ x ∈ R, u * x * u⁻¹ = x → x ∈ Z) :
    Nat.card R ≡ Nat.card ↥(R ⊓ Z) [MOD r] := by
  let f : R → R := fun x => ⟨u * x * u⁻¹, hR x x.2⟩
  have hiter : ∀ (n : ℕ) (x : R), ((f^[n] x : R) : G) = u ^ n * x * (u ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', pow_succ]
      show u * ((f^[n] x : R) : G) * u⁻¹ = _
      rw [ih]
      group
  have hf : ∀ x, f^[r] x = x := fun x => Subtype.ext (by rw [hiter, hu]; group)
  have hmod := card_modEq_fix_prime r f hf
  have hcard : Nat.card {a | f a = a} = Nat.card ↥(R ⊓ Z) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨(a.1 : G), a.1.2, hfix a.1 a.1.2 (congrArg Subtype.val a.2)⟩
        invFun := fun y => ⟨⟨(y : G), y.2.1⟩, Subtype.ext (hZu y y.2.2)⟩
        left_inv := fun a => rfl
        right_inv := fun y => rfl }
  rw [hcard] at hmod
  exact hmod

end Lower

section TwentyTwo

variable {W : Type} [CommGroup W] [Finite W]

local instance : Finite (MulAut W) :=
  Finite.of_injective (fun σ : MulAut W => (σ : W → W)) DFunLike.coe_injective

open scoped commutatorElement

private theorem orderOf_two_zmod_three' : orderOf (2 : ZMod 3) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m
  decide

theorem two_pow_22_le_card_of_fixfree (hW : ∀ w : W, w * w = 1) {U Z : Subgroup (MulAut W)}
    {u : MulAut W} (hZU : Z ≤ U) (hZc : ∀ z ∈ Z, ∀ f ∈ U, f * z = z * f)
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ Z) (hpow : ∀ a ∈ U, a ^ 3 ∈ Z)
    (hZcard : Nat.card Z = 1 ∨ Nat.card Z = 3)
    (hUcard : Nat.card U = 243 * Nat.card Z) (hZu : ∀ z ∈ Z, u * z * u⁻¹ = z)
    (hu11 : u ^ 11 = 1) (hu1 : u ≠ 1) (huU : ∀ x ∈ U, u * x * u⁻¹ ∈ U)
    (hfix : ∀ x ∈ U, u * x * u⁻¹ = x → x ∈ Z) : 2 ^ 22 ≤ Nat.card W := by
  classical
  have h3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set T : Subgroup (MulAut W) := Subgroup.zpowers u with hT
  have hpowU : ∀ n : ℕ, ∀ x ∈ U, u ^ n * x * (u ^ n)⁻¹ ∈ U := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have := ih _ (huU x hx)
      rw [pow_succ, mul_inv_rev]
      convert this using 1
      group
  have hTU' : ∀ t ∈ T, ∀ x ∈ U, t * x * t⁻¹ ∈ U := by
    intro t ht x hx
    rw [hT, ← mem_powers_iff_mem_zpowers] at ht
    obtain ⟨n, rfl⟩ := ht
    exact hpowU n x hx
  have hTU : T ≤ Subgroup.normalizer (U : Set (MulAut W)) := le_normalizer_of_conj_mem hTU'
  have hord : orderOf u = 11 := orderOf_eq_prime hu11 hu1
  have hTcard : Nat.card T = 11 := by rw [hT, Nat.card_zpowers, hord]
  have hmod : ∀ R : Subgroup (MulAut W), R ≤ U → (∀ x ∈ R, u * x * u⁻¹ ∈ R) →
      Nat.card R ≡ Nat.card ↥(R ⊓ Z) [MOD 11] := fun R hRU hR =>
    card_modEq_inf_of_conj 11 hu11 R Z hR hZu fun x hx hux => hfix x (hRU hx) hux
  have hUe : (∀ a ∈ U, ∀ b ∈ U, a * b = b * a) ∧ ∀ a ∈ U, a ^ 3 = 1 := by
    rcases hZcard with hZ | hZ
    · have hZbot : Z = ⊥ := Subgroup.card_eq_one.1 hZ
      refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
      · have := hcomm a ha b hb
        rw [hZbot, Subgroup.mem_bot] at this
        exact commutatorElement_eq_one_iff_mul_comm.1 this
      · have := hpow a ha
        rwa [hZbot, Subgroup.mem_bot] at this
    · refine commutative_exponent_of_cover (p := 3) (F := U) (Z := Z) (T := T) hZU hZc hZ
        hcomm hpow (n := 3) (by norm_num) (by rw [hUcard, hZ]; norm_num) hTU'
        (fun t ht => T.inv_mem ht) ?_
      intro R hZR hRU hRT
      have hRu : ∀ x ∈ R, u * x * u⁻¹ ∈ R := fun x hx => hRT u (Subgroup.mem_zpowers u) x hx
      have hm := hmod R hRU hRu
      rw [inf_eq_right.2 hZR, hZ] at hm
      have hdvd : Nat.card R ∣ 3 ^ 6 := by
        have := Subgroup.card_dvd_of_le hRU
        rw [hUcard, hZ] at this
        simpa using this
      obtain ⟨j, hj, hjR⟩ := (Nat.dvd_prime_pow h3.out).1 hdvd
      rw [hjR] at hm
      interval_cases j
      · exact absurd hm (by decide)
      · left
        exact (Subgroup.eq_of_le_of_card_ge hZR (by rw [hjR, hZ]; norm_num)).symm
      · exact absurd hm (by decide)
      · exact absurd hm (by decide)
      · exact absurd hm (by decide)
      · exact absurd hm (by decide)
      · right
        exact Subgroup.eq_of_le_of_card_ge hRU (by rw [hjR, hUcard, hZ]; norm_num)
  obtain ⟨hUc, hUp⟩ := hUe
  have horb : ∀ D : Subgroup (MulAut W), D ≤ U → D.relIndex U = 3 →
      ¬ T ≤ Subgroup.normalizer (D : Set (MulAut W)) →
      11 ≤ (T ⊓ Subgroup.normalizer (D : Set (MulAut W))).relIndex T := by
    intro D _ _ hD
    set H := T ⊓ Subgroup.normalizer (D : Set (MulAut W)) with hH
    have h1 := H.relIndex_mul_card T
    rw [inf_eq_left.2 (inf_le_left : H ≤ T)] at h1
    have hdvd : Nat.card H ∣ 11 := hTcard ▸ Subgroup.card_dvd_of_le (inf_le_left : H ≤ T)
    rcases (Nat.dvd_prime h11.out).1 hdvd with h | h
    · rw [h, mul_one, hTcard] at h1
      omega
    · exfalso
      apply hD
      have : H = T := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hTcard])
      rw [← this]
      exact inf_le_right
  have hhyper : ∀ D : Subgroup (MulAut W), D ≤ U → D.relIndex U = 3 →
      T ≤ Subgroup.normalizer (D : Set (MulAut W)) →
      Nat.card Z = 3 ∧ Nat.card ↥(D ⊓ Z) = 1 := by
    intro D hDU hD hDT
    have hcard : 3 * Nat.card D = Nat.card U := by
      have := D.relIndex_mul_card U
      rwa [hD, inf_eq_left.2 hDU] at this
    have hinv : ∀ x ∈ D, u * x * u⁻¹ ∈ D := fun x hx =>
      conj_mem_of_le_normalizer hDT (Subgroup.mem_zpowers u) hx
    have hm := hmod D hDU hinv
    have hdvd : Nat.card ↥(D ⊓ Z) ∣ Nat.card Z := Subgroup.card_dvd_of_le inf_le_right
    rcases hZcard with hZ | hZ
    · exfalso
      have h1 : Nat.card ↥(D ⊓ Z) = 1 := by
        rw [hZ] at hdvd
        exact Nat.dvd_one.1 hdvd
      have h2 : Nat.card D = 81 := by rw [hZ] at hUcard; omega
      rw [h2, h1] at hm
      exact absurd hm (by decide)
    · refine ⟨hZ, ?_⟩
      rw [hZ] at hdvd
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hdvd with h | h
      · exact h
      · exfalso
        have h2 : Nat.card D = 243 := by rw [hZ] at hUcard; omega
        rw [h2, h] at hm
        exact absurd hm (by decide)
  have hcore : ∃ x ∈ U, x ≠ 1 ∧ ∀ D : Subgroup (MulAut W), D ≤ U → D.relIndex U = 3 →
      T ≤ Subgroup.normalizer (D : Set (MulAut W)) → x ∈ D := by
    rcases hZcard with hZ | hZ
    · have hUne : U ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hUcard
        omega
      obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hUne
      refine ⟨x, hx, fun h => hx1 (Subtype.ext h), fun D hDU hD hDT => ?_⟩
      exact absurd (hhyper D hDU hD hDT).1 (by omega)
    · refine exists_mem_invariant_hyperplanes_of_cover (p := 3) (Z := Z) (T := T) hUc hZU hZ
        (by omega) ?_ ?_
      · intro t ht z hz
        rw [hT, ← mem_powers_iff_mem_zpowers] at ht
        obtain ⟨n, rfl⟩ := ht
        have hcomm' : Commute (u ^ n) z := (Commute.pow_left (show Commute u z from by
          have := hZu z hz
          calc u * z = (u * z * u⁻¹) * u := by group
            _ = z * u := by rw [this]) n)
        rw [hcomm'.eq]
        simpa using hz
      · intro D hDU hD hDT hZD
        have := (hhyper D hDU hD hDT).2
        have hle : D ⊓ Z = Z := inf_eq_right.2 hZD
        rw [hle, hZ] at this
        omega
  have := two_pow_le_card_of_hyperplane_cover hW (p := 3) (by norm_num) hUc hUp hTU horb hcore
  rwa [orderOf_two_zmod_three'] at this

end TwentyTwo

section Lift

variable {W : Type} [CommGroup W] [Finite W]

local instance : Finite (MulAut W) :=
  Finite.of_injective (fun σ : MulAut W => (σ : W → W)) DFunLike.coe_injective

open scoped commutatorElement

theorem card_comap_of_surjective' {L S : Type*} [Group L] [Group S] [Finite L] (π : L →* S)
    (hπ : Function.Surjective π) (A : Subgroup S) :
    Nat.card (A.comap π) = Nat.card A * Nat.card π.ker := by
  classical
  set R : Subgroup L := A.comap π with hR
  have hker : π.ker ≤ R := fun k hk => by
    rw [hR, Subgroup.mem_comap, MonoidHom.mem_ker.mp hk]
    exact A.one_mem
  have hmap : R.map π = A := Subgroup.map_comap_eq_self_of_surjective hπ A
  have h1 := Subgroup.card_mul_index (π.ker.subgroupOf R)
  have h2 : (π.ker.subgroupOf R).index = Nat.card A := by
    have : (π.ker.subgroupOf R) = (π.comp R.subtype).ker := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [this, Subgroup.index_ker, MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  have h3 : Nat.card (π.ker.subgroupOf R) = Nat.card π.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv
  rw [h2, h3] at h1
  rw [← h1, mul_comm]

theorem two_pow_22_le_card_of_cover (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    {S : Type} [Group S] (e : CQ L ≃* S)
    (hZ : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3)
    {A : Subgroup S} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAp : ∀ a ∈ A, a ^ 3 = 1)
    (hAcard : Nat.card A = 243) {g : S} (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hg11 : g ^ 11 = 1)
    (hgnc : ∃ a ∈ A, g * a * g⁻¹ ≠ a) : 2 ^ 22 ≤ Nat.card W := by
  classical
  have h3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let π : ↥L →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥L := by
    ext x
    simp [π]
  have : Finite S := Finite.of_surjective π hπ
  have hCA : ∀ a ∈ A, g * a * g⁻¹ = a → a = 1 := by
    have hm := card_modEq_inf_of_conj 11 hg11 A (Subgroup.centralizer {g}) hgA
      (fun z hz => by
        have := Subgroup.mem_centralizer_iff.1 hz g (Set.mem_singleton g)
        calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [this]
          _ = z := by group)
      (fun x _ hx => by
        refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
        rw [Set.mem_singleton_iff.1 hh]
        calc g * x = (g * x * g⁻¹) * g := by group
          _ = x * g := by rw [hx])
    rw [hAcard] at hm
    have hdvd : Nat.card ↥(A ⊓ Subgroup.centralizer {g}) ∣ 3 ^ 5 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : A ⊓ Subgroup.centralizer {g} ≤ A)
      rwa [hAcard] at this
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow h3.out).1 hdvd
    rw [hjc] at hm
    intro a ha hag
    interval_cases j
    · have h1 : A ⊓ Subgroup.centralizer {g} = ⊥ := Subgroup.card_eq_one.1 (by simpa using hjc)
      have : a ∈ A ⊓ Subgroup.centralizer {g} := by
        refine ⟨ha, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
        rw [Set.mem_singleton_iff.1 hh]
        calc g * a = (g * a * g⁻¹) * g := by group
          _ = a * g := by rw [hag]
      rw [h1, Subgroup.mem_bot] at this
      exact this
    all_goals try exact absurd hm (by decide)
    exfalso
    obtain ⟨a₀, ha₀, hne⟩ := hgnc
    have hall : A ⊓ Subgroup.centralizer {g} = A :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : A ⊓ Subgroup.centralizer {g} ≤ A)
        (by rw [hjc, hAcard]; norm_num)
    have : a₀ ∈ A ⊓ Subgroup.centralizer {g} := by rw [hall]; exact ha₀
    have h2 := Subgroup.mem_centralizer_iff.1 this.2 g (Set.mem_singleton g)
    apply hne
    calc g * a₀ * g⁻¹ = (a₀ * g) * g⁻¹ := by rw [h2]
      _ = a₀ := by group
  have hKp : ¬ 11 ∣ Nat.card π.ker := by
    rw [hker]
    rcases hZ with h | h <;> rw [h] <;> norm_num
  obtain ⟨l, hl, hl11⟩ := exists_map_eq_pow_eq_one π hπ hKp hg11
  set F : Subgroup ↥L := A.comap π with hF
  have hFmem : ∀ x : ↥L, x ∈ F ↔ π x ∈ A := fun x => Iff.rfl
  have hFcard : Nat.card F = 243 * Nat.card (Subgroup.center ↥L) := by
    rw [hF, card_comap_of_surjective' π hπ A, hAcard, hker]
  set U : Subgroup (MulAut W) := F.map L.subtype with hU
  set Z' : Subgroup (MulAut W) := (Subgroup.center ↥L).map L.subtype with hZ'
  have hUmem : ∀ x : MulAut W, x ∈ U ↔ ∃ y : ↥L, π y ∈ A ∧ (y : MulAut W) = x := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  have hZ'mem : ∀ x : MulAut W, x ∈ Z' ↔ ∃ y : ↥L, y ∈ Subgroup.center ↥L ∧ (y : MulAut W) = x := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  have hUcard : Nat.card U = 243 * Nat.card Z' := by
    rw [hU, hZ', Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective L.subtype_injective, hFcard]
  have hZ'card : Nat.card Z' = 1 ∨ Nat.card Z' = 3 := by
    rw [hZ', Subgroup.card_map_of_injective L.subtype_injective]
    exact hZ
  have hcentral : ∀ y : ↥L, y ∈ Subgroup.center ↥L → π y = 1 := fun y hy => by
    rw [← MonoidHom.mem_ker, hker]; exact hy
  have hZ'U : Z' ≤ U := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hZ'mem x).1 hx
    exact (hUmem _).2 ⟨y, by rw [hcentral y hy]; exact A.one_mem, rfl⟩
  have hZ'c : ∀ z ∈ Z', ∀ f ∈ U, f * z = z * f := by
    intro z hz f _
    obtain ⟨y, hy, rfl⟩ := (hZ'mem z).1 hz
    obtain ⟨y', _, rfl⟩ := (hUmem f).1 ‹f ∈ U›
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hy y')
  have hcommU : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ Z' := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := (hUmem a).1 ha
    obtain ⟨y, hy, rfl⟩ := (hUmem b).1 hb
    refine (hZ'mem _).2 ⟨⁅x, y⁆, ?_, rfl⟩
    rw [← hker, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hAc _ hx _ hy)
  have hpowU : ∀ a ∈ U, a ^ 3 ∈ Z' := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := (hUmem a).1 ha
    refine (hZ'mem _).2 ⟨x ^ 3, ?_, rfl⟩
    rw [← hker, MonoidHom.mem_ker, map_pow]
    exact hAp _ hx
  have hZu : ∀ z ∈ Z', (l : MulAut W) * z * (l : MulAut W)⁻¹ = z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := (hZ'mem z).1 hz
    have this : (l : MulAut W) * (y : MulAut W) = (y : MulAut W) * (l : MulAut W) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hy l)
    calc (l : MulAut W) * (y : MulAut W) * (l : MulAut W)⁻¹ =
        ((y : MulAut W) * (l : MulAut W)) * (l : MulAut W)⁻¹ := by rw [this]
      _ = y := by group
  have hu11 : (l : MulAut W) ^ 11 = 1 := by
    have := congrArg Subtype.val hl11
    simpa using this
  have hu1 : (l : MulAut W) ≠ 1 := by
    intro h
    have hl1 : l = 1 := Subtype.ext h
    obtain ⟨a₀, -, hne⟩ := hgnc
    apply hne
    have : g = 1 := by rw [← hl, hl1, map_one]
    rw [this]
    group
  have huU : ∀ x ∈ U, (l : MulAut W) * x * (l : MulAut W)⁻¹ ∈ U := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hUmem x).1 hx
    refine (hUmem _).2 ⟨l * y * l⁻¹, ?_, rfl⟩
    rw [map_mul, map_mul, map_inv, hl]
    exact hgA _ hy
  have hfix : ∀ x ∈ U, (l : MulAut W) * x * (l : MulAut W)⁻¹ = x → x ∈ Z' := by
    intro x hx hlx
    obtain ⟨y, hy, rfl⟩ := (hUmem x).1 hx
    have h1 : l * y * l⁻¹ = y := Subtype.ext hlx
    have h2 : g * π y * g⁻¹ = π y := by
      have := congrArg π h1
      rwa [map_mul, map_mul, map_inv, hl] at this
    have h3 : π y = 1 := hCA _ hy h2
    refine (hZ'mem _).2 ⟨y, ?_, rfl⟩
    rw [← hker]
    exact h3
  exact two_pow_22_le_card_of_fixfree hW hZ'U hZ'c hcommU hpowU hZ'card hUcard hZu hu11 hu1 huU
    hfix

end Lift

section Assembly

variable {W : Type} [CommGroup W] [Finite W]

theorem exclusion_of_three_generation (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hq : CFSG.IsQuasisimple ↥L) (hirr : IsIrrOn L) {S : Type} [Group S] (e : CQ L ≃* S)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    (hZ : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3)
    (hgen : ∀ ψ : MulAut S, ψ * ψ = 1 → ψ ≠ 1 → ∃ cs : List S, cs.length = 3 ∧
      (MulAut.conj : S →* MulAut S).range ≤ Subgroup.closure
        {x : MulAut S | ∃ c ∈ cs, x = MulAut.conj c * ψ * (MulAut.conj c)⁻¹})
    (hrank : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 6)
    {A : Subgroup S} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAp : ∀ a ∈ A, a ^ 3 = 1)
    (hAcard : Nat.card A = 243) {g : S} (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hg11 : g ^ 11 = 1)
    (hgnc : ∃ a ∈ A, g * a * g⁻¹ ≠ a) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  classical
  have hfinW : Finite (MulAut W) :=
    Finite.of_injective (fun σ : MulAut W => (σ : W → W)) DFunLike.coe_injective
  have hperf : Group.IsPerfect ↥L := hq.1
  have hL : L ≠ ⊥ := ne_bot_of_isQuasisimple hq
  apply weight_lt_of_lt_index
  by_contra hcon
  push Not at hcon
  have : Finite S := Finite.of_equiv _ e.toEquiv
  have : Finite (MulAut S) :=
    Finite.of_injective (fun f : MulAut S => (f : S → S)) (fun f g h => MulEquiv.ext (congrFun h))
  let Φ : ↥E →* MulAut S := psiHom L e hE
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx2 : (x : MulAut W) * (x : MulAut W) = 1 := by
      have := hEel.2 x x.2
      rwa [sq] at this
    have hxc : ∀ l ∈ L, l * (x : MulAut W) = (x : MulAut W) * l :=
      commutes_of_psiAut_eq_one hperf e (hE x.2) hx
    exact Subtype.ext (eq_one_of_commutes_of_sq_eq_one hW hirr hxc hx2)
  have hEcard : Nat.card E ≤ 2 ^ 6 := by
    have hB : Nat.card Φ.range ≤ 2 ^ 6 := by
      refine hrank _ ?_ ?_
      · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hEel.1 a a.2 b b.2)
      · rintro _ ⟨a, rfl⟩
        rw [← map_mul]
        have : a * a = 1 := Subtype.ext (by have := hEel.2 a a.2; simpa [pow_two] using this)
        rw [this, map_one]
    rw [Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv]
    exact hB
  obtain ⟨⟨b, hbE⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hb2 : b * b = 1 := by
    have := hEel.2 b hbE
    rwa [sq] at this
  have hψ2 : psiAut L e (hE hbE) * psiAut L e (hE hbE) = 1 := by
    have hbb : b * b ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.normalizer (L : Set (MulAut W))).mul_mem (hE hbE) (hE hbE)
    have key : ∀ (c : MulAut W) (hc : c ∈ Subgroup.normalizer (L : Set (MulAut W))), c = 1 →
        psiAut L e hc = 1 := by
      rintro c hc rfl
      exact psiAut_one e hc
    rw [← psiAut_mul e (hE hbE) (hE hbE) hbb]
    exact key _ hbb hb2
  have hψ1 : psiAut L e (hE hbE) ≠ 1 := by
    intro h
    have hxc : ∀ l ∈ L, l * b = b * l := commutes_of_psiAut_eq_one hperf e (hE hbE) h
    exact hb1' (eq_one_of_commutes_of_sq_eq_one hW hirr hxc hb2)
  obtain ⟨cs, hcs, hcsgen⟩ := hgen _ hψ2 hψ1
  have hW18 := card_le_index_pow_of_psi_generation hW hperf hirr hL hE hEel e hbE cs hcsgen
  rw [hcs] at hW18
  have hmono : (fixV (Subgroup.zpowers b)).index ≤ (fixV E).index :=
    Subgroup.index_antitone (CFSG.Quasithin.fixV_anti ((Subgroup.zpowers_le).2 hbE))
  have hidx : (fixV (Subgroup.zpowers b)).index ≤ 2 ^ 6 := hmono.trans (hcon.trans hEcard)
  have h18 : Nat.card W ≤ (2 ^ 6) ^ 3 := hW18.trans (Nat.pow_le_pow_left hidx 3)
  have h22 := two_pow_22_le_card_of_cover hW e hZ hAc hAp hAcard hgA hg11 hgnc
  norm_num at h18
  omega

end Assembly

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
