module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

namespace SRAut

section Generic

theorem inverted_lift_aux {Γ : Type*} [Group Γ] (τ x : Γ) (Z : Subgroup Γ) (hτ : τ * τ = 1)
    (hZc : ∀ z ∈ Z, x * z = z * x) (hZo : ∀ z ∈ Z, Odd (orderOf z)) (m : ℕ) (hm : Odd m)
    (hxm : x ^ m ∈ Z) (hinv : τ * x * τ⁻¹ * x ∈ Z) :
    ∃ z ∈ Z, Odd (orderOf (x * z)) ∧ τ * (x * z) * τ⁻¹ = (x * z)⁻¹ := by
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  rw [hτi] at hinv ⊢
  obtain ⟨w, hw⟩ : ∃ w, w = τ * x * τ * x := ⟨_, rfl⟩
  rw [← hw] at hinv
  have hxw : x * w = w * x := hZc w hinv
  have hτw : τ * w * τ = w := by
    have h1 : τ * w * τ = x * τ * x * τ := by
      calc τ * w * τ = (τ * τ) * x * τ * x * τ := by rw [hw]; group
        _ = x * τ * x * τ := by rw [hτ, one_mul]
    have h2 : x * τ * x * τ = w := by
      have : x * τ * x * τ * x = w * x := by
        rw [← hxw, hw]; group
      exact mul_right_cancel this
    rw [h1, h2]
  obtain ⟨r, hr⟩ := hZo w hinv
  obtain ⟨z, hz⟩ : ∃ z, z = w ^ r := ⟨_, rfl⟩
  have hzZ : z ∈ Z := hz ▸ Subgroup.pow_mem Z hinv r
  have hw2 : w * z * z = 1 := by
    have : w * z * z = w ^ (2 * r + 1) := by
      rw [hz, ← pow_succ', ← pow_add]
      congr 1
      ring
    rw [this, ← hr, pow_orderOf_eq_one]
  have hτz : τ * z * τ = z := by
    have : τ * w ^ r * τ = (τ * w * τ) ^ r := by
      have := conj_pow (a := τ) (b := w) (i := r)
      rw [hτi] at this
      exact this.symm
    rw [hz, this, hτw]
  have hxz : x * z = z * x := hZc z hzZ
  have hxz' : x⁻¹ * z = z * x⁻¹ := by
    calc x⁻¹ * z = x⁻¹ * (z * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * z) * x⁻¹ := by rw [hxz]
      _ = z * x⁻¹ := by group
  refine ⟨z, hzZ, ?_, ?_⟩
  · have hpow : (x * z) ^ m = x ^ m * z ^ m := Commute.mul_pow hxz m
    have hmZ : (x * z) ^ m ∈ Z := by
      rw [hpow]
      exact Z.mul_mem hxm (Subgroup.pow_mem Z hzZ m)
    have hodd := hZo _ hmZ
    have hdvd : orderOf (x * z) ∣ m * orderOf ((x * z) ^ m) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, pow_orderOf_eq_one]
    exact Odd.of_dvd_nat (hm.mul hodd) hdvd
  · have e1 : τ * x * τ = w * x⁻¹ := by rw [hw]; group
    have h3 : w * z = z⁻¹ := eq_inv_of_mul_eq_one_left hw2
    calc τ * (x * z) * τ = τ * x * 1 * z * τ := by group
      _ = τ * x * (τ * τ) * z * τ := by rw [hτ]
      _ = (τ * x * τ) * (τ * z * τ) := by group
      _ = w * x⁻¹ * z := by rw [e1, hτz]
      _ = w * z * x⁻¹ := by rw [mul_assoc, hxz', ← mul_assoc]
      _ = z⁻¹ * x⁻¹ := by rw [h3]
      _ = (x * z)⁻¹ := by rw [mul_inv_rev]

end Generic

section Setting
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

@[expose] noncomputable def rhoK (hR : Red28 W K S) : ↥K →* MulAut ↥(vOf W K S) :=
  (vAct hR).comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ S))

theorem rhoK_apply (hR : Red28 W K S) (k : ↥K) (v : ↥(vOf W K S)) :
    (((rhoK hR k) v : ↥(vOf W K S)) : X) = (k : X) * (v : X) * (k : X)⁻¹ := rfl

theorem rhoK_of_mem_W (hR : Red28 W K S) (k : ↥K) (hk : (k : X) ∈ W) : rhoK hR k = 1 := by
  refine MulEquiv.ext fun v => Subtype.ext ?_
  have hc : (v : X) * (k : X) = (k : X) * (v : X) := v.2.2.1 (k : X) (hR.w1_le hk)
  show (k : X) * (v : X) * (k : X)⁻¹ = (v : X)
  rw [← hc]
  group

theorem mem_zPre_of_rhoK_eq_one (hR : Red28 W K S) (k : ↥K) (h1 : rhoK hR k = 1) :
    (k : X) ∈ zPre W K := by
  refine ⟨k.2, fun k' hk' => hR.cent_comm k (Subgroup.mem_sup_left k.2) (fun v hv => ?_) k' hk'⟩
  have := congrArg (fun f : MulAut ↥(vOf W K S) => ((f ⟨v, hv⟩ : ↥(vOf W K S)) : X)) h1
  simp only [rhoK_apply, MulAut.one_apply] at this
  calc (k : X) * v = ((k : X) * v * (k : X)⁻¹) * (k : X) := by group
    _ = v * k := by rw [this]

theorem toBar_eq_one_iff (k : ↥K) : toBar W K k = 1 ↔ (k : X) ∈ W := by
  constructor
  · intro h
    have h' : ((toBar W K k : ↥(bar W K)) : X ⧸ W) = 1 := by rw [h]; rfl
    exact (QuotientGroup.eq_one_iff _).1 h'
  · intro h
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).2 h

theorem toBar_surjective (W K : Subgroup X) [W.Normal] : Function.Surjective (toBar W K) := by
  rintro ⟨y, k, hk, rfl⟩
  exact ⟨⟨k, hk⟩, rfl⟩

theorem mem_zPre_iff (k : ↥K) :
    (k : X) ∈ zPre W K ↔ toBar W K k ∈ Subgroup.center ↥(bar W K) := by
  have key : ∀ k' : ↥K, (⁅(k : X), (k' : X)⁆ ∈ W ↔
      toBar W K k' * toBar W K k = toBar W K k * toBar W K k') := by
    intro k'
    have h1 : ((⁅k, k'⁆ : ↥K) : X) = ⁅(k : X), (k' : X)⁆ := rfl
    rw [← h1, ← toBar_eq_one_iff, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm,
      eq_comm]
  rw [Subgroup.mem_center_iff]
  constructor
  · rintro ⟨-, hk⟩ g
    obtain ⟨k', rfl⟩ := toBar_surjective W K g
    exact (key k').1 (hk k' k'.2)
  · intro h
    exact ⟨k.2, fun k' hk' => (key ⟨k', hk'⟩).2 (h _)⟩

theorem modC_eq_one_iff (k : ↥K) : modC W K k = 1 ↔ (k : X) ∈ zPre W K := by
  rw [mem_zPre_iff]
  exact QuotientGroup.eq_one_iff _

theorem central_odd_of_pCore_bot {G : Type*} [Group G] [Finite G] (h : CFSG.pCore 2 G = ⊥) {z : G}
    (hz : z ∈ Subgroup.center G) : Odd (orderOf z) := by
  by_contra hodd
  have hev : 2 ∣ orderOf z := by
    rcases Nat.even_or_odd (orderOf z) with h' | h'
    · exact even_iff_two_dvd.mp h'
    · exact absurd h' hodd
  have hpos : orderOf z ≠ 0 := (orderOf_pos z).ne'
  have h2 : orderOf (z ^ (orderOf z / 2)) = 2 := orderOf_pow_orderOf_div hpos hev
  obtain ⟨w, hw⟩ : ∃ w, w = z ^ (orderOf z / 2) := ⟨_, rfl⟩
  rw [← hw] at h2
  have hwc : w ∈ Subgroup.center G := hw ▸ Subgroup.pow_mem _ hz _
  have hN : (Subgroup.zpowers w).Normal :=
    Subgroup.normal_of_le_center (by rw [Subgroup.zpowers_le]; exact hwc)
  have hP : IsPGroup 2 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2]; norm_num)
  have hle : Subgroup.zpowers w ≤ CFSG.pCore 2 G := le_sSup ⟨hN, hP⟩
  rw [h] at hle
  have h3 : w ∈ (⊥ : Subgroup G) := hle (Subgroup.mem_zpowers w)
  rw [Subgroup.mem_bot] at h3
  rw [h3, orderOf_one] at h2
  omega

theorem orderOf_rhoK_odd (h : Setup28 W K S) (hR : Red28 W K S) (k : ↥K)
    (hk : (k : X) ∈ zPre W K) : Odd (orderOf (rhoK hR k)) := by
  have hc : toBar W K k ∈ Subgroup.center ↥(bar W K) := (mem_zPre_iff k).1 hk
  have hodd := central_odd_of_pCore_bot h.hO hc
  have h1 : rhoK hR k ^ orderOf (toBar W K k) = 1 := by
    have h2 : toBar W K (k ^ orderOf (toBar W K k)) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    rw [toBar_eq_one_iff] at h2
    rw [← map_pow]
    exact rhoK_of_mem_W hR _ h2
  exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one h1)

theorem inverts_to_aut_aux (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    (ha2 : a ^ 2 = 1) {P : ℕ → Prop} (hinv : Inverts W K a P) :
    ∃ y : MulAut ↥(vOf W K S), Odd (orderOf y) ∧ (∃ m, Odd m ∧ P m ∧ m ∣ orderOf y) ∧
      vAct hR ⟨a, Subgroup.mem_sup_right haS⟩ * y * (vAct hR ⟨a, Subgroup.mem_sup_right haS⟩)⁻¹ =
        y⁻¹ := by
  obtain ⟨x, hxodd, hxP, hxz⟩ := hinv
  have haN : a ∈ K ⊔ S := Subgroup.mem_sup_right haS
  obtain ⟨m, hm⟩ : ∃ m, m = orderOf (modC W K x) := ⟨_, rfl⟩
  rw [← hm] at hxodd hxP
  have hτ : vAct hR ⟨a, haN⟩ * vAct hR ⟨a, haN⟩ = 1 := vAct_sq hR haN ha2
  let Z : Subgroup (MulAut ↥(vOf W K S)) := ((zPre W K).subgroupOf K).map (rhoK hR)
  have hZmem : ∀ z ∈ Z, ∃ k : ↥K, (k : X) ∈ zPre W K ∧ rhoK hR k = z := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hz
    exact ⟨k, hk, rfl⟩
  have hZc : ∀ z ∈ Z, rhoK hR x * z = z * rhoK hR x := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := hZmem z hz
    have h1 : rhoK hR ⁅k, x⁆ = 1 := rhoK_of_mem_W hR _ (hk.2 x x.2)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hZo : ∀ z ∈ Z, Odd (orderOf z) := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := hZmem z hz
    exact orderOf_rhoK_odd h hR k hk
  have hxm : rhoK hR x ^ m ∈ Z := by
    have h1 : modC W K (x ^ m) = 1 := by rw [map_pow, hm, pow_orderOf_eq_one]
    have h2 : ((x ^ m : ↥K) : X) ∈ zPre W K := (modC_eq_one_iff _).1 h1
    exact Subgroup.mem_map.2 ⟨x ^ m, Subgroup.mem_subgroupOf.2 h2, by rw [map_pow]⟩
  have hinvZ : vAct hR ⟨a, haN⟩ * rhoK hR x * (vAct hR ⟨a, haN⟩)⁻¹ * rhoK hR x ∈ Z := by
    have hk0 : a * (x : X) * a⁻¹ * (x : X) ∈ K := hxz.1
    refine Subgroup.mem_map.2 ⟨⟨_, hk0⟩, Subgroup.mem_subgroupOf.2 hxz, ?_⟩
    have e : (⟨a * (x : X) * a⁻¹ * (x : X), Subgroup.mem_sup_left hk0⟩ : ↥(K ⊔ S)) =
        ⟨a, haN⟩ * ⟨(x : X), Subgroup.mem_sup_left x.2⟩ * ⟨a, haN⟩⁻¹ *
          ⟨(x : X), Subgroup.mem_sup_left x.2⟩ := rfl
    show vAct hR ⟨_, Subgroup.mem_sup_left hk0⟩ = _
    rw [e, map_mul, map_mul, map_mul, map_inv]
    rfl
  obtain ⟨z, hzZ, hzodd, hzinv⟩ :=
    inverted_lift_aux (vAct hR ⟨a, haN⟩) (rhoK hR x) Z hτ hZc hZo m hxodd hxm hinvZ
  obtain ⟨k₁, hk₁, rfl⟩ := hZmem z hzZ
  refine ⟨rhoK hR x * rhoK hR k₁, hzodd, ⟨m, hxodd, hxP, ?_⟩, hzinv⟩
  obtain ⟨e, he⟩ : ∃ e, e = orderOf (rhoK hR x * rhoK hR k₁) := ⟨_, rfl⟩
  rw [← he]
  have h1 : rhoK hR (x * k₁) ^ e = 1 := by
    rw [map_mul, he]
    exact pow_orderOf_eq_one _
  rw [← map_pow] at h1
  have h2 : (((x * k₁) ^ e : ↥K) : X) ∈ zPre W K := mem_zPre_of_rhoK_eq_one hR _ h1
  have h3 : modC W K ((x * k₁) ^ e) = 1 := (modC_eq_one_iff _).2 h2
  have h4 : modC W K k₁ = 1 := (modC_eq_one_iff _).2 hk₁
  rw [map_pow, map_mul, h4, mul_one] at h3
  rw [hm]
  exact orderOf_dvd_of_pow_eq_one h3

theorem inverts_five_contra_aux (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    (ha2 : a ^ 2 = 1) (htr : TransvOn (vOf W K S) a)
    (hinv : Inverts W K a (fun m => m = 5)) : False := by
  obtain ⟨y, hyodd, ⟨m, -, hm5, hmy⟩, hyinv⟩ := inverts_to_aut_aux h hR haS ha2 hinv
  have h5y : 5 ∣ orderOf y := hm5 ▸ hmy
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at h5y
    omega
  obtain ⟨u, huV, hu1, htu⟩ := htr
  by_cases hτ1 : vAct hR ⟨a, Subgroup.mem_sup_right haS⟩ = 1
  · rw [hτ1, one_mul, inv_one, mul_one] at hyinv
    have hy2 : y * y = 1 := by
      calc y * y = y⁻¹ * y := by rw [← hyinv]
        _ = 1 := inv_mul_cancel y
    have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
    have := dvd_trans h5y h2
    omega
  · letI : CommGroup ↥(vOf W K S) :=
      { (inferInstance : Group ↥(vOf W K S)) with
        mul_comm := fun a b => by
          have := hR.v_elem.1
          exact mul_comm' a b }
    have hV2 : ∀ v : ↥(vOf W K S), v ^ 2 = 1 := fun v =>
      Subtype.ext (by simpa using hR.v_elem.2 v v.2)
    have hT : CFSG.Quasithin.IsTransvectionWith (vAct hR ⟨a, Subgroup.mem_sup_right haS⟩)
        (⟨u, huV⟩ : ↥(vOf W K S)) := by
      refine ⟨fun h1 => hu1 (congrArg Subtype.val h1), fun v => ?_⟩
      rcases htu v v.2 with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1)
    obtain ⟨-, -, -, hy3⟩ := CFSG.Quasithin.B1.inverted_by_transvection hV2 hT hτ1 hyodd
      (pow_orderOf_eq_one y) hy1 hyinv
    have h3 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    have := dvd_trans h5y h3
    omega

theorem finite_mulAut (G : Type*) [Group G] [Finite G] : Finite (MulAut G) :=
  inferInstanceAs (Finite (G ≃* G))

theorem relIndex_le_card_indAut (h : Setup28 W K S) {A : Subgroup X} (hAS : A ≤ S) :
    (kerAct W K S).relIndex A ≤ Nat.card ↥(indAut W K A) := by
  haveI : Finite (MulAut ↥(bar W K)) := finite_mulAut _
  have hmem : ∀ a : ↥A, (QuotientGroup.mk (a : X) : X ⧸ W) ∈
      Subgroup.normalizer ((bar W K : Subgroup (X ⧸ W)) : Set (X ⧸ W)) := fun a =>
    K.le_normalizer_map (QuotientGroup.mk' W) (Subgroup.mem_map_of_mem _ (h.hN (hAS a.2)))
  let g : ↥A →* ↥(Subgroup.normalizer ((bar W K : Subgroup (X ⧸ W)) : Set (X ⧸ W))) :=
    { toFun := fun a => ⟨QuotientGroup.mk (a : X), hmem a⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  let φ : ↥A →* MulAut ↥(bar W K) := (bar W K).normalizerMonoidHom.comp g
  have hker : φ.ker ≤ (kerAct W K S).subgroupOf A := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    refine Subgroup.mem_subgroupOf.2 ⟨hAS a.2, fun k hk => ?_⟩
    have h1 : (QuotientGroup.mk (a : X) : X ⧸ W) * QuotientGroup.mk k *
        (QuotientGroup.mk (a : X))⁻¹ = QuotientGroup.mk k := by
      have := congrArg (fun f : MulAut ↥(bar W K) =>
        ((f (toBar W K ⟨k, hk⟩) : ↥(bar W K)) : X ⧸ W)) ha
      exact this
    have h2 : (QuotientGroup.mk ((a : X) * k * (a : X)⁻¹ * k⁻¹) : X ⧸ W) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [h1, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).1 h2
  have hrange : φ.range ≤ indAut W K A := by
    rintro _ ⟨a, rfl⟩
    exact Subgroup.mem_map.2 ⟨g a, Subgroup.mem_subgroupOf.2 ⟨a, a.2, rfl⟩, rfl⟩
  haveI : Finite ↥(indAut W K A) := inferInstance
  calc (kerAct W K S).relIndex A = ((kerAct W K S).subgroupOf A).index := rfl
    _ ≤ φ.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          (Subgroup.index_dvd_of_le hker)
    _ = Nat.card φ.range := Subgroup.index_ker φ
    _ ≤ Nat.card ↥(indAut W K A) := Subgroup.card_le_of_le hrange

theorem offender_fix_index_aux (h : Setup28 W K S) (hR : Red28 W K S) {A : Subgroup X}
    (hA : Off28 W K S A) (hc : Nat.card ↥(indAut W K A) = 4) {a : X} (haA : a ∈ A) :
    (fixV' (Subgroup.zpowers (vAct hR ⟨a, Subgroup.mem_sup_right (hA.isMax.1 haA)⟩))).index ≤ 4 := by
  have h1 : (kerAct W K S).relIndex A ≤ 4 := hc ▸ relIndex_le_card_indAut h hA.isMax.1
  have h2 := hA.off.trans h1
  have hle : (Subgroup.centralizer (A : Set X)).subgroupOf (vOf W K S) ≤
      fixV' (Subgroup.zpowers (vAct hR ⟨a, Subgroup.mem_sup_right (hA.isMax.1 haA)⟩)) := by
    intro v hv x hx
    have hva : ∀ b ∈ A, b * (v : X) = (v : X) * b :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hv)
    have hτ : vAct hR ⟨a, Subgroup.mem_sup_right (hA.isMax.1 haA)⟩ v = v := by
      refine Subtype.ext ?_
      show a * (v : X) * a⁻¹ = (v : X)
      rw [hva a haA]
      group
    have hle' : Subgroup.zpowers (vAct hR ⟨a, Subgroup.mem_sup_right (hA.isMax.1 haA)⟩) ≤
        MulAction.stabilizer (MulAut ↥(vOf W K S)) v :=
      (Subgroup.zpowers_le).2 (by rw [MulAction.mem_stabilizer_iff]; exact hτ)
    have := hle' hx
    rwa [MulAction.mem_stabilizer_iff] at this
  calc (fixV' (Subgroup.zpowers (vAct hR ⟨a, Subgroup.mem_sup_right (hA.isMax.1 haA)⟩))).index
      ≤ ((Subgroup.centralizer (A : Set X)).subgroupOf (vOf W K S)).index :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          (Subgroup.index_dvd_of_le hle)
    _ = (Subgroup.centralizer (A : Set X)).relIndex (vOf W K S) := rfl
    _ ≤ 4 := h2

end Setting

end SRAut

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
