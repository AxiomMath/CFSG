module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Api
public import CFSG.LocalAnalysis.GLTheoremB.I2810.BlocksChief

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.Hyp3Aux

section Generic

theorem aut_eq_one_of_trivial_modZ' {G : Type} [Group G] (hG : commutator G = ⊤) {Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) (α : MulAut G) (h : ∀ x : G, x⁻¹ * α x ∈ Z) : α = 1 := by
  have hc : ∀ x y : G, y * (x⁻¹ * α x) = (x⁻¹ * α x) * y := fun x y =>
    Subgroup.mem_center_iff.mp (hZ (h x)) y
  let f : G →* G :=
    { toFun := fun x => x⁻¹ * α x
      map_one' := by simp
      map_mul' := fun x y => by
        have := hc x y⁻¹
        simp only [mul_inv_rev, map_mul]
        calc y⁻¹ * x⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [this]
          _ = _ := by group }
  have hker : commutator G ≤ f.ker := by
    show ⁅(⊤ : Subgroup G), ⊤⁆ ≤ f.ker
    refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc g₂ (f g₁)
  ext x
  have hx : x ∈ f.ker := hker (hG ▸ Subgroup.mem_top x)
  rw [MonoidHom.mem_ker] at hx
  simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, inv_mul_eq_one] at hx
  simpa using hx.symm

theorem normal_le_center_of_twoPower {G : Type} [Group G] [Finite G] (hperf : commutator G = ⊤)
    (hsimple : IsSimpleGroup (G ⧸ Subgroup.center G))
    (Q : Subgroup G) [Q.Normal]
    (hQ : ∀ q ∈ Q, ∃ i : ℕ, q ^ 2 ^ i ∈ Subgroup.center G) : Q ≤ Subgroup.center G := by
  have hnorm : (Q.map (QuotientGroup.mk' (Subgroup.center G))).Normal :=
    Subgroup.Normal.map ‹_› _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (Q.map (QuotientGroup.mk' (Subgroup.center G)))
    with hbot | htop
  · intro q hq'
    have : QuotientGroup.mk' (Subgroup.center G) q ∈ (⊥ : Subgroup _) := hbot ▸ ⟨q, hq', rfl⟩
    exact (QuotientGroup.eq_one_iff q).1 (Subgroup.mem_bot.1 this)
  · exfalso
    have hp : IsPGroup 2 (G ⧸ Subgroup.center G) := by
      intro y
      have hy : y ∈ Q.map (QuotientGroup.mk' (Subgroup.center G)) := htop ▸ Subgroup.mem_top y
      obtain ⟨q, hq', rfl⟩ := hy
      obtain ⟨i, hi⟩ := hQ q hq'
      exact ⟨i, by rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).2 hi⟩
    haveI : Group.IsNilpotent (G ⧸ Subgroup.center G) := hp.isNilpotent
    haveI : Group.IsPerfect G := Group.isPerfect_def.2 hperf
    haveI : Group.IsPerfect (G ⧸ Subgroup.center G) := inferInstance
    haveI : Nontrivial (G ⧸ Subgroup.center G) := hsimple.toNontrivial
    exact Group.IsPerfect.not_isSolvable (G ⧸ Subgroup.center G) inferInstance

end Generic

section Quotient
variable {X : Type} [Group X] {W K : Subgroup X} [W.Normal]

theorem toBar_coe' (k : ↥K) : ((toBar W K k : ↥(bar W K)) : X ⧸ W) = QuotientGroup.mk (k : X) := rfl

theorem toBar_eq_iff' {k k' : ↥K} : toBar W K k = toBar W K k' ↔ (k : X)⁻¹ * k' ∈ W := by
  rw [← Subtype.coe_inj, toBar_coe', toBar_coe', QuotientGroup.eq]

theorem mk_mem_normalizer_bar' {b : X} (hb : b ∈ Subgroup.normalizer (K : Set X)) :
    (QuotientGroup.mk b : X ⧸ W) ∈
      Subgroup.normalizer ((bar W K : Subgroup (X ⧸ W)) : Set (X ⧸ W)) :=
  Subgroup.le_normalizer_map (QuotientGroup.mk' W) ⟨b, hb, rfl⟩

variable (W) in
@[expose] noncomputable def indOf {b : X} (hb : b ∈ Subgroup.normalizer (K : Set X)) :
    MulAut ↥(bar W K) :=
  (bar W K).normalizerMonoidHom ⟨QuotientGroup.mk b, mk_mem_normalizer_bar' hb⟩

theorem indOf_coe {b : X} (hb : b ∈ Subgroup.normalizer (K : Set X)) (y : ↥(bar W K)) :
    ((indOf W hb y : ↥(bar W K)) : X ⧸ W) =
      QuotientGroup.mk b * (y : X ⧸ W) * (QuotientGroup.mk b)⁻¹ := rfl

theorem indOf_toBar {b : X} (hb : b ∈ Subgroup.normalizer (K : Set X)) (k k' : ↥K)
    (hk' : (k' : X) = b * k * b⁻¹) : indOf W hb (toBar W K k) = toBar W K k' := by
  apply Subtype.ext
  rw [indOf_coe, toBar_coe', toBar_coe', hk']
  simp

theorem indOf_mem_indAut {B : Subgroup X} (hB : B ≤ Subgroup.normalizer (K : Set X)) {b : X}
    (hb : b ∈ B) : indOf W (hB hb) ∈ indAut W K B :=
  (mem_indAut_iff hB _).2 ⟨b, hb, fun k k' hk' => indOf_toBar (hB hb) k k' hk'⟩

theorem indOf_eq_one_iff {b : X} (hb : b ∈ Subgroup.normalizer (K : Set X)) :
    indOf W hb = 1 ↔ ∀ k ∈ K, ⁅b, k⁆ ∈ W := by
  constructor
  · intro h1 k hk
    have hk' : b * k * b⁻¹ ∈ K := (Subgroup.mem_set_normalizer_iff.1 hb k).1 hk
    have h2 := indOf_toBar (W := W) hb ⟨k, hk⟩ ⟨b * k * b⁻¹, hk'⟩ rfl
    rw [h1, MulAut.one_apply] at h2
    have h3 : (k : X)⁻¹ * (b * k * b⁻¹) ∈ W := (toBar_eq_iff' (W := W) (K := K)).1 h2
    have h4 : ⁅b, k⁆ = k * ((k : X)⁻¹ * (b * k * b⁻¹)) * k⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h4]
    exact (inferInstance : W.Normal).conj_mem _ h3 k
  · intro h1
    ext y
    obtain ⟨k, rfl⟩ := (toBar_props W K).1 y
    have hk' : b * (k : X) * b⁻¹ ∈ K := (Subgroup.mem_set_normalizer_iff.1 hb k).1 k.2
    rw [indOf_toBar (W := W) hb k ⟨b * k * b⁻¹, hk'⟩ rfl, MulAut.one_apply]
    symm
    refine congrArg Subtype.val ((toBar_eq_iff' (W := W) (K := K)).2 ?_)
    have h2 := h1 k k.2
    have h4 : (k : X)⁻¹ * (b * (k : X) * b⁻¹) = (k : X)⁻¹ * ⁅b, (k : X)⁆ * (k : X) := by
      simp only [commutatorElement_def]; group
    show (k : X)⁻¹ * (b * (k : X) * b⁻¹) ∈ W
    rw [h4]
    simpa using (inferInstance : W.Normal).conj_mem _ h2 (k : X)⁻¹

end Quotient

section VAct
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem vAct_apply_coe (hR : Red28 W K S) (n : ↥(K ⊔ S)) (v : ↥(vOf W K S)) :
    ((vAct hR n v : ↥(vOf W K S)) : X) = (n : X) * v * (n : X)⁻¹ := rfl

theorem vAct_eq_one_iff (hR : Red28 W K S) (n : ↥(K ⊔ S)) :
    vAct hR n = 1 ↔ ∀ v ∈ vOf W K S, (n : X) * v = v * (n : X) := by
  constructor
  · intro h v hv
    have h1 : vAct hR n ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [h]; rfl
    have h2 := congrArg Subtype.val h1
    rw [vAct_apply_coe] at h2
    calc (n : X) * v = ((n : X) * v * (n : X)⁻¹) * n := by group
      _ = v * n := by rw [h2]
  · intro h
    ext v
    rw [vAct_apply_coe]
    have := h v v.2
    show (n : X) * v * (n : X)⁻¹ = v
    rw [this]; group

theorem mem_khOf_iff (hR : Red28 W K S) (g : MulAut ↥(vOf W K S)) :
    g ∈ khOf hR ↔ ∃ k : ↥K, g = vAct hR (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ S) k) := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, hn⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨Subgroup.inclusion (le_sup_left : K ≤ K ⊔ S) k, k.2, rfl⟩

theorem mem_ehOf_iff (hR : Red28 W K S) {A : Subgroup X} (g : MulAut ↥(vOf W K S)) :
    g ∈ ehOf hR A ↔ ∃ (a : X) (ha : a ∈ K ⊔ S), a ∈ A ∧ g = vAct hR ⟨a, ha⟩ := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, n.2, hn, rfl⟩
  · rintro ⟨a, ha, haA, rfl⟩
    exact ⟨⟨a, ha⟩, haA, rfl⟩

theorem kToKh_surjective (hR : Red28 W K S) : Function.Surjective (kToKh hR) := by
  rintro ⟨g, hg⟩
  obtain ⟨k, rfl⟩ := (mem_khOf_iff hR g).1 hg
  exact ⟨k, Subtype.ext rfl⟩

theorem kToKh_eq_one_iff (hR : Red28 W K S) (k : ↥K) :
    kToKh hR k = 1 ↔ ∀ v ∈ vOf W K S, (k : X) * v = v * (k : X) := by
  have key := vAct_eq_one_iff hR (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ S) k)
  exact ⟨fun h => key.1 (congrArg Subtype.val h), fun h => Subtype.ext (key.2 h)⟩

theorem mem_zPre_of_kToKh_eq_one (hR : Red28 W K S) {k : ↥K} (hk : kToKh hR k = 1) :
    (k : X) ∈ zPre W K :=
  ⟨k.2, fun k' hk' =>
    hR.cent_comm k (Subgroup.mem_sup_left k.2) ((kToKh_eq_one_iff hR k).1 hk) k' hk'⟩

theorem kToKh_eq_one_of_mem_W (hR : Red28 W K S) {k : ↥K} (hk : (k : X) ∈ W) : kToKh hR k = 1 :=
  (kToKh_eq_one_iff hR k).2 fun v hv => (hv.2.1 k (hR.w1_le hk)).symm

theorem kToKh_mem_center_of_zPre (hR : Red28 W K S) {k : ↥K} (hk : (k : X) ∈ zPre W K) :
    kToKh hR k ∈ Subgroup.center ↥(khOf hR) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨k', rfl⟩ := kToKh_surjective hR g
  have h1 : kToKh hR ⁅k, k'⁆ = 1 := kToKh_eq_one_of_mem_W hR (hk.2 k' k'.2)
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem mem_zPre_of_kToKh_mem_center (hR : Red28 W K S) {k : ↥K}
    (hk : kToKh hR k ∈ Subgroup.center ↥(khOf hR)) : (k : X) ∈ zPre W K := by
  have hperf : commutator ↥(bar W K) = ⊤ := hR.quasi.1.commutator_eq_top
  refine (zPre_iff_center k).2 ?_
  have hα : (MulAut.conj (toBar W K k) : MulAut ↥(bar W K)) = 1 := by
    refine aut_eq_one_of_trivial_modZ' hperf (le_refl _) _ fun x => ?_
    obtain ⟨k', rfl⟩ := (toBar_props W K).1 x
    have hc : kToKh hR (k'⁻¹ * (k * k' * k⁻¹)) = 1 := by
      have hcomm := Subgroup.mem_center_iff.1 hk (kToKh hR k')
      simp only [map_mul, map_inv]
      calc (kToKh hR k')⁻¹ * (kToKh hR k * kToKh hR k' * (kToKh hR k)⁻¹)
          = (kToKh hR k')⁻¹ * ((kToKh hR k * kToKh hR k') * (kToKh hR k)⁻¹) := by group
        _ = 1 := by rw [← hcomm]; group
    have hz := (zPre_iff_center _).1 (mem_zPre_of_kToKh_eq_one hR hc)
    have : (toBar W K k')⁻¹ * (MulAut.conj (toBar W K k)) (toBar W K k') =
        toBar W K (k'⁻¹ * (k * k' * k⁻¹)) := by
      simp [MulAut.conj_apply, map_mul, map_inv]
    rw [this]; exact hz
  rw [Subgroup.mem_center_iff]
  intro g
  have := congrArg (fun φ : MulAut ↥(bar W K) => φ g) hα
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc g * toBar W K k = (toBar W K k * g * (toBar W K k)⁻¹) * toBar W K k := by rw [this]
    _ = toBar W K k * g := by group

end VAct

section Basic
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem khOf_perfect (h : Setup28 W K S) (hR : Red28 W K S) : ⁅khOf hR, khOf hR⁆ = khOf hR := by
  haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 h.hK.2.1
  haveI : Group.IsPerfect ↥(khOf hR) := Group.IsPerfect.ofSurjective (kToKh_surjective hR)
  exact Subgroup.isPerfect_iff.1 inferInstance

theorem khOf_ne_bot (hR : Red28 W K S) : khOf hR ≠ ⊥ := by
  intro hbot
  apply hR.v_nt
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 : kToKh hR ⟨k, hk⟩ = 1 :=
    Subtype.ext (Subgroup.mem_bot.1 (hbot ▸ (kToKh hR ⟨k, hk⟩).2))
  exact ((kToKh_eq_one_iff hR ⟨k, hk⟩).1 h1 v hv).symm

theorem pCore_khOf (h : Setup28 W K S) (hR : Red28 W K S) : CFSG.pCore 2 ↥(khOf hR) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨κ, rfl⟩ := kToKh_surjective hR x
  have hPn : (CFSG.pCore 2 ↥(khOf hR)).Normal := CFSG.pCore_normal
  have hPp : IsPGroup 2 ↥(CFSG.pCore 2 ↥(khOf hR)) := CFSG.pCore_isPGroup
  haveI : ((CFSG.pCore 2 ↥(khOf hR)).comap (kToKh hR)).Normal := hPn.comap _
  haveI : (((CFSG.pCore 2 ↥(khOf hR)).comap (kToKh hR)).map (toBar W K)).Normal :=
    Subgroup.Normal.map ‹_› _ (toBar_props W K).1
  have hQ : ∀ q ∈ ((CFSG.pCore 2 ↥(khOf hR)).comap (kToKh hR)).map (toBar W K),
      ∃ i : ℕ, q ^ 2 ^ i ∈ Subgroup.center ↥(bar W K) := by
    rintro q ⟨κ', hκ', rfl⟩
    obtain ⟨i, hi⟩ := hPp ⟨kToKh hR κ', hκ'⟩
    refine ⟨i, ?_⟩
    have h1 : kToKh hR (κ' ^ 2 ^ i) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hi
    rw [← map_pow]
    exact (zPre_iff_center _).1 (mem_zPre_of_kToKh_eq_one hR h1)
  have hcen := normal_le_center_of_twoPower hR.quasi.1.commutator_eq_top hR.quasi.2.1 _ hQ
  have hκz : toBar W K κ ∈ Subgroup.center ↥(bar W K) := hcen ⟨κ, hx, rfl⟩
  set N := Nat.card ↥(Subgroup.center ↥(bar W K)) with hN
  have hNodd : Odd N := BlocksChief.centre_odd_aux h
  have hpow : (toBar W K κ) ^ N = 1 := by
    have h1 : ((⟨toBar W K κ, hκz⟩ : ↥(Subgroup.center ↥(bar W K))) ^ N : ↥(Subgroup.center ↥(bar W K))) = 1 :=
      pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  have hW : ((κ ^ N : ↥K) : X) ∈ W := by
    rw [← (toBar_props W K).2, map_pow]; exact hpow
  have hxN : (kToKh hR κ) ^ N = 1 := by
    rw [← map_pow]; exact kToKh_eq_one_of_mem_W hR hW
  obtain ⟨j, hj⟩ := hPp ⟨kToKh hR κ, hx⟩
  have hj' : (kToKh hR κ) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hcop : Nat.Coprime (2 ^ j) N := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hNodd)
  have hd : orderOf (kToKh hR κ) ∣ Nat.gcd (2 ^ j) N :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_of_pow_eq_one hxN)
  rw [hcop] at hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

end Basic


section EhOf
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem vAct_conj_incl (hR : Red28 W K S) {a : X} (ha : a ∈ K ⊔ S) (k k' : ↥K)
    (hk' : (k' : X) = a * k * a⁻¹) :
    vAct hR ⟨a, ha⟩ * vAct hR (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ S) k) *
      (vAct hR ⟨a, ha⟩)⁻¹ = vAct hR (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ S) k') := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp [hk']

theorem kToKh_conj (hR : Red28 W K S) {a : X} (ha : a ∈ K ⊔ S) (k k' : ↥K)
    (hk' : (k' : X) = a * k * a⁻¹) :
    ((kToKh hR k' : ↥(khOf hR)) : MulAut ↥(vOf W K S)) =
      vAct hR ⟨a, ha⟩ * (kToKh hR k : MulAut ↥(vOf W K S)) * (vAct hR ⟨a, ha⟩)⁻¹ :=
  (vAct_conj_incl hR ha k k' hk').symm

theorem conj_mem_khOf (hR : Red28 W K S) {a : X} (ha : a ∈ K ⊔ S)
    (haN : a ∈ Subgroup.normalizer (K : Set X)) {g : MulAut ↥(vOf W K S)} (hg : g ∈ khOf hR) :
    vAct hR ⟨a, ha⟩ * g * (vAct hR ⟨a, ha⟩)⁻¹ ∈ khOf hR := by
  obtain ⟨k, rfl⟩ := (mem_khOf_iff hR g).1 hg
  have hk' : a * (k : X) * a⁻¹ ∈ K := (Subgroup.mem_set_normalizer_iff.1 haN k).1 k.2
  rw [vAct_conj_incl hR ha k ⟨a * k * a⁻¹, hk'⟩ rfl]
  exact (mem_khOf_iff hR _).2 ⟨_, rfl⟩

theorem ehOf_le_normalizer (h : Setup28 W K S) (hR : Red28 W K S) {A : Subgroup X} (hAS : A ≤ S) :
    ehOf hR A ≤ Subgroup.normalizer (khOf hR : Set (MulAut ↥(vOf W K S))) := by
  intro ε hε
  obtain ⟨a, ha, haA, rfl⟩ := (mem_ehOf_iff hR ε).1 hε
  have haN : a ∈ Subgroup.normalizer (K : Set X) := h.hN (hAS haA)
  have hainvA : a⁻¹ ∈ A := A.inv_mem haA
  have hainvN : a⁻¹ ∈ Subgroup.normalizer (K : Set X) := h.hN (hAS hainvA)
  have hainv : a⁻¹ ∈ K ⊔ S := (K ⊔ S).inv_mem ha
  rw [Subgroup.mem_set_normalizer_iff]
  intro g
  refine ⟨fun hg => conj_mem_khOf hR ha haN hg, fun hg => ?_⟩
  have h1 := conj_mem_khOf hR hainv hainvN hg
  have e1 : vAct hR ⟨a⁻¹, hainv⟩ = (vAct hR ⟨a, ha⟩)⁻¹ := by
    rw [← map_inv]; rfl
  rw [e1] at h1
  have e2 : (vAct hR ⟨a, ha⟩)⁻¹ * (vAct hR ⟨a, ha⟩ * g * (vAct hR ⟨a, ha⟩)⁻¹) *
      ((vAct hR ⟨a, ha⟩)⁻¹)⁻¹ = g := by group
  rwa [e2] at h1

theorem vAct_eq_one_iff_mem_kerAct (hR : Red28 W K S) {a : X} (ha : a ∈ K ⊔ S) (haS : a ∈ S) :
    vAct hR ⟨a, ha⟩ = 1 ↔ a ∈ kerAct W K S := by
  rw [vAct_eq_one_iff]
  constructor
  · intro hc
    exact ⟨haS, fun k hk => hR.cent_comm a ha hc k hk⟩
  · intro hk v hv
    exact (hv.2.1 a hk).symm

theorem ehOf_faithful (h : Setup28 W K S) (hR : Red28 W K S) {A : Subgroup X} (hAS : A ≤ S)
    {ε : MulAut ↥(vOf W K S)} (hε : ε ∈ ehOf hR A)
    (hc : ∀ k ∈ khOf hR, ε * k = k * ε) : ε = 1 := by
  obtain ⟨a, ha, haA, rfl⟩ := (mem_ehOf_iff hR ε).1 hε
  have haN : a ∈ Subgroup.normalizer (K : Set X) := h.hN (hAS haA)
  have hperf : commutator ↥(bar W K) = ⊤ := hR.quasi.1.commutator_eq_top
  have hconj : ∀ k : ↥K, ∀ k' : ↥K, (k' : X) = a * k * a⁻¹ → kToKh hR (k⁻¹ * k') = 1 := by
    intro k k' hk'
    have h1 := kToKh_conj hR ha k k' hk'
    have h2 := hc _ (kToKh hR k).2
    have h3 : ((kToKh hR k' : ↥(khOf hR)) : MulAut ↥(vOf W K S)) =
        ((kToKh hR k : ↥(khOf hR)) : MulAut ↥(vOf W K S)) := by
      rw [h1]
      calc vAct hR ⟨a, ha⟩ * (kToKh hR k : MulAut ↥(vOf W K S)) * (vAct hR ⟨a, ha⟩)⁻¹
          = (vAct hR ⟨a, ha⟩ * (kToKh hR k : MulAut ↥(vOf W K S))) * (vAct hR ⟨a, ha⟩)⁻¹ := rfl
        _ = ((kToKh hR k : MulAut ↥(vOf W K S)) * vAct hR ⟨a, ha⟩) * (vAct hR ⟨a, ha⟩)⁻¹ := by
          rw [h2]
        _ = (kToKh hR k : MulAut ↥(vOf W K S)) := by group
    have h4 : kToKh hR k' = kToKh hR k := Subtype.ext h3
    rw [map_mul, map_inv, h4]; group
  have hα : indOf W haN = 1 := by
    refine aut_eq_one_of_trivial_modZ' hperf (le_refl _) _ fun x => ?_
    obtain ⟨k, rfl⟩ := (toBar_props W K).1 x
    have hk' : a * (k : X) * a⁻¹ ∈ K := (Subgroup.mem_set_normalizer_iff.1 haN k).1 k.2
    rw [indOf_toBar (W := W) haN k ⟨a * k * a⁻¹, hk'⟩ rfl, ← map_inv, ← map_mul]
    exact (zPre_iff_center _).1 (mem_zPre_of_kToKh_eq_one hR (hconj k ⟨a * k * a⁻¹, hk'⟩ rfl))
  have haW : ∀ k ∈ K, ⁅a, k⁆ ∈ W := by
    intro k hk
    have hk' : a * k * a⁻¹ ∈ K := (Subgroup.mem_set_normalizer_iff.1 haN k).1 hk
    have h1 := indOf_toBar (W := W) haN ⟨k, hk⟩ ⟨a * k * a⁻¹, hk'⟩ rfl
    rw [hα, MulAut.one_apply] at h1
    have h2 := (toBar_eq_iff'.1 h1)
    have h3 : (k : X)⁻¹ * (a * k * a⁻¹) ∈ W := h2
    have h4 : ⁅a, k⁆ = k * ((k : X)⁻¹ * (a * k * a⁻¹)) * k⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h4]
    exact (inferInstance : W.Normal).conj_mem _ h3 k
  exact (vAct_eq_one_iff_mem_kerAct hR ha (hAS haA)).2 ⟨hAS haA, haW⟩

end EhOf

section Card
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem card_ehOf (hR : Red28 W K S) {A : Subgroup X} (hAS : A ≤ S) :
    Nat.card ↥(ehOf hR A) = (kerAct W K S).relIndex A := by
  let f : ↥A →* MulAut ↥(vOf W K S) :=
    (vAct hR).comp (Subgroup.inclusion (hAS.trans le_sup_right))
  have hrange : ehOf hR A = f.range := by
    ext g
    rw [mem_ehOf_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨a, ha, haA, rfl⟩
      exact ⟨⟨a, haA⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, hAS.trans le_sup_right a.2, a.2, rfl⟩
  have hker : f.ker = (kerAct W K S).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact vAct_eq_one_iff_mem_kerAct hR _ (hAS a.2)
  rw [hrange, ← Subgroup.index_ker, hker]
  rfl

theorem fixV'_ehOf (hR : Red28 W K S) {A : Subgroup X} (hA : A ≤ K ⊔ S) :
    fixV' (ehOf hR A) = (Subgroup.centralizer (A : Set X)).subgroupOf (vOf W K S) := by
  ext v
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hv a ha
    have h1 : vAct hR ⟨a, hA ha⟩ v = v := hv _ ((mem_ehOf_iff hR _).2 ⟨a, hA ha, ha, rfl⟩)
    have h2 := congrArg Subtype.val h1
    rw [vAct_apply_coe] at h2
    calc a * (v : X) = (a * v * a⁻¹) * a := by group
      _ = v * a := by rw [h2]
  · intro hv ε hε
    obtain ⟨a, ha, haA, rfl⟩ := (mem_ehOf_iff hR ε).1 hε
    apply Subtype.ext
    rw [vAct_apply_coe]
    have := hv a haA
    show a * (v : X) * a⁻¹ = v
    rw [this]; group

theorem fixV'_index_le (hR : Red28 W K S) {A : Subgroup X} (hA : Off28 W K S A) :
    (fixV' (ehOf hR A)).index ≤ Nat.card ↥(ehOf hR A) := by
  rw [fixV'_ehOf hR (hA.isMax.1.trans le_sup_right), card_ehOf hR hA.isMax.1]
  exact hA.off

end Card

section Act
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem act_transfer (hR : Red28 W K S) {n : ℕ}
    (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n)))
    (π : ↥(khOf hR) →* ↥(alternatingGroup (Fin n)))
    (hπ : ∀ k : ↥K, π (kToKh hR k) = e (modC W K k)) {a : X} (ha : a ∈ K ⊔ S)
    (haN : a ∈ Subgroup.normalizer (K : Set X)) (v : ↥(alternatingGroup (Fin n))) :
    (∀ k k' : ↥K, (k' : X) = a * k * a⁻¹ → e (modC W K k') = v * e (modC W K k) * v⁻¹) ↔
    (∀ k k' : ↥(khOf hR),
      (k' : MulAut ↥(vOf W K S)) = vAct hR ⟨a, ha⟩ * k * (vAct hR ⟨a, ha⟩)⁻¹ →
        π k' = v * π k * v⁻¹) := by
  constructor
  · intro hK k k' hkk'
    obtain ⟨κ, rfl⟩ := kToKh_surjective hR k
    obtain ⟨κ', rfl⟩ := kToKh_surjective hR k'
    have hl : a * (κ : X) * a⁻¹ ∈ K := (Subgroup.mem_set_normalizer_iff.1 haN κ).1 κ.2
    have h1 := kToKh_conj hR ha κ ⟨a * κ * a⁻¹, hl⟩ rfl
    have h2 : kToKh hR κ' = kToKh hR ⟨a * κ * a⁻¹, hl⟩ := Subtype.ext (hkk'.trans h1.symm)
    rw [h2, hπ, hπ]
    exact hK κ ⟨a * κ * a⁻¹, hl⟩ rfl
  · intro hK k k' hkk'
    have h1 := hK (kToKh hR k) (kToKh hR k') (kToKh_conj hR ha k k' hkk')
    rwa [hπ, hπ] at h1

theorem exists_v_of_act (h : Setup28 W K S) {n : ℕ}
    {e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))}
    {Vs : Subgroup ↥(alternatingGroup (Fin n))}
    (hact : ∀ φ ∈ indAut W K S, ∃ σ ∈ Vs.map (MulAut.conj : ↥(alternatingGroup (Fin n)) →* _),
      InducesOn e φ σ) {a : X} (haS : a ∈ S) :
    ∃ v ∈ Vs, ∀ k k' : ↥K, (k' : X) = a * k * a⁻¹ →
      e (modC W K k') = v * e (modC W K k) * v⁻¹ := by
  have hφ := indOf_mem_indAut (W := W) (K := K) h.hN haS
  obtain ⟨σ, ⟨v, hv, rfl⟩, hσ⟩ := hact _ hφ
  refine ⟨v, hv, fun k k' hk' => ?_⟩
  have h1 := hσ (toBar W K k)
  rw [indOf_toBar (h.hN haS) k k' hk'] at h1
  simpa [modC, MulAut.conj_apply] using h1

variable (W K) in
@[expose] def vvOf {A : Subgroup X} (hAN : A ≤ Subgroup.normalizer (K : Set X)) {n : ℕ}
    (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n)))
    (Vs : Subgroup ↥(alternatingGroup (Fin n))) : Subgroup ↥(alternatingGroup (Fin n)) where
  carrier := {v | v ∈ Vs ∧ ∃ a ∈ A, ∀ k k' : ↥K, (k' : X) = a * k * a⁻¹ →
    e (modC W K k') = v * e (modC W K k) * v⁻¹}
  one_mem' := ⟨Vs.one_mem, 1, A.one_mem, fun k k' hk' => by
    have : k' = k := Subtype.ext (by simpa using hk')
    simp [this]⟩
  mul_mem' := by
    rintro v₁ v₂ ⟨hv₁, a₁, ha₁, h₁⟩ ⟨hv₂, a₂, ha₂, h₂⟩
    refine ⟨Vs.mul_mem hv₁ hv₂, a₁ * a₂, A.mul_mem ha₁ ha₂, fun k k' hk' => ?_⟩
    have hl : a₂ * (k : X) * a₂⁻¹ ∈ K := (Subgroup.mem_set_normalizer_iff.1 (hAN ha₂) k).1 k.2
    have e1 : (k' : X) = a₁ * ((a₂ * (k : X) * a₂⁻¹ : X)) * a₁⁻¹ := by rw [hk']; group
    rw [h₁ ⟨a₂ * k * a₂⁻¹, hl⟩ k' e1, h₂ k ⟨a₂ * k * a₂⁻¹, hl⟩ rfl]
    group
  inv_mem' := by
    rintro v ⟨hv, a, ha, h₁⟩
    refine ⟨Vs.inv_mem hv, a⁻¹, A.inv_mem ha, fun k k' hk' => ?_⟩
    have e1 : (k : X) = a * (k' : X) * a⁻¹ := by rw [hk']; group
    have := h₁ k' k e1
    rw [inv_inv, show e (modC W K k') = v⁻¹ * e (modC W K k) * v by rw [this]; group]

end Act

section A7
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem commV'_map (hR : Red28 W K S) :
    (commV' (khOf hR)).map (vOf W K S).subtype = ⁅vOf W K S, K⁆ := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro c ⟨x, hx, v, rfl⟩
    obtain ⟨k, rfl⟩ := (mem_khOf_iff hR x).1 hx
    show ((vAct hR (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ S) k) v * v⁻¹ : ↥(vOf W K S)) : X) ∈
      ⁅vOf W K S, K⁆
    have e1 : ((vAct hR (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ S) k) v * v⁻¹ :
        ↥(vOf W K S)) : X) = ⁅(k : X), (v : X)⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, vAct_apply_coe, commutatorElement_def]
      rfl
    rw [e1, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator k.2 v.2
  · refine Subgroup.commutator_le.2 fun v hv k hk => ?_
    refine ⟨(vAct hR (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ S) ⟨k, hk⟩) ⟨v, hv⟩ *
      (⟨v, hv⟩ : ↥(vOf W K S))⁻¹)⁻¹, ?_, ?_⟩
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure
        ⟨_, (mem_khOf_iff hR _).2 ⟨⟨k, hk⟩, rfl⟩, ⟨v, hv⟩, rfl⟩)
    · simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul, vAct_apply_coe,
        commutatorElement_def]
      show (k * v * k⁻¹ * v⁻¹)⁻¹ = v * k * v⁻¹ * k⁻¹
      group

theorem commV'_invariant (hR : Red28 W K S) {g : MulAut ↥(vOf W K S)} (hg : g ∈ khOf hR)
    {y : ↥(vOf W K S)} (hy : y ∈ commV' (khOf hR)) : g y ∈ commV' (khOf hR) := by
  induction hy using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, v, rfl⟩ := hc
    refine Subgroup.subset_closure ⟨g * x * g⁻¹, ?_, g v, ?_⟩
    · exact (khOf hR).mul_mem ((khOf hR).mul_mem hg hx) ((khOf hR).inv_mem hg)
    · simp
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem a7x_of_struct (h : Setup28 W K S) (hR : Red28 W K S) (hs : A7Struct (khOf hR)) :
    A7X W K S := by
  have hmap := commV'_map hR
  have hle : ⁅vOf W K S, K⁆ ≤ vOf W K S := by
    rw [← hmap]; exact Subgroup.map_subtype_le _
  have hcard : Nat.card ↥⁅vOf W K S, K⁆ = 16 := by
    rw [← hmap, Subgroup.card_map_of_injective (vOf W K S).subtype_injective]
    exact hs.comm16
  have hinv : ∀ k ∈ K, ∀ x ∈ ⁅vOf W K S, K⁆, k * x * k⁻¹ ∈ ⁅vOf W K S, K⁆ := by
    intro k hk x hx
    rw [← hmap] at hx ⊢
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨vAct hR (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ S) ⟨k, hk⟩) u,
      commV'_invariant hR ((mem_khOf_iff hR _).2 ⟨⟨k, hk⟩, rfl⟩) hu, rfl⟩
  have hfix : (∀ k ∈ K, ∀ x ∈ ⁅vOf W K S, K⁆, ⁅x, k⁆ = 1) → False := by
    intro hall
    have hfixed : ∀ g ∈ khOf hR, ∀ y ∈ commV' (khOf hR), g y = y := by
      intro g hg y hy
      obtain ⟨k, rfl⟩ := (mem_khOf_iff hR g).1 hg
      have hy' : (y : X) ∈ ⁅vOf W K S, K⁆ := by rw [← hmap]; exact ⟨y, hy, rfl⟩
      have h1 := commutatorElement_eq_one_iff_mul_comm.1 (hall k k.2 y hy')
      apply Subtype.ext
      rw [vAct_apply_coe]
      show (k : X) * y * (k : X)⁻¹ = y
      rw [mul_inv_eq_iff_eq_mul, ← h1]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : 2 ∣ Nat.card ↥(commV' (khOf hR)) := by rw [hs.comm16]; norm_num
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hyord : orderOf (y : ↥(vOf W K S)) = 2 := by rw [Subgroup.orderOf_coe, hy]
    have hYle : Subgroup.zpowers (y : ↥(vOf W K S)) ≤ commV' (khOf hR) := by
      rw [Subgroup.zpowers_le]; exact y.2
    have hYinv : ∀ g ∈ khOf hR, ∀ z ∈ Subgroup.zpowers (y : ↥(vOf W K S)), g z ∈
        Subgroup.zpowers (y : ↥(vOf W K S)) := fun g hg z hz => by
      rw [hfixed g hg z (hYle hz)]; exact hz
    rcases hs.irred _ hYle hYinv with hb | ht
    · have h1 : (y : ↥(vOf W K S)) = 1 := Subgroup.zpowers_eq_bot.1 hb
      rw [h1, orderOf_one] at hyord
      omega
    · have h3 : Nat.card ↥(Subgroup.zpowers (y : ↥(vOf W K S))) = 2 := by
        rw [Nat.card_zpowers, hyord]
      rw [ht, hs.comm16] at h3
      omega
  refine ⟨⟨⟨⟨bot_le, hle⟩, hinv, fun k hk x hx => ?_, fun k hk x hx => ?_,
    fun k hk v hv => Subgroup.commutator_mem_commutator hv hk, ?_⟩, ?_⟩, hcard, ?_⟩
  · rw [Subgroup.mem_bot.1 hx]; simp
  · rw [Subgroup.mem_bot.1 hx]; simp
  · by_contra hn
    push Not at hn
    exact hfix fun k hk x hx => Subgroup.mem_bot.1 (hn k hk x hx)
  · intro Y _ hYU hYinv
    have hY'le : Y.subgroupOf (vOf W K S) ≤ commV' (khOf hR) := by
      intro y hy
      have h1 : (y : X) ∈ ⁅vOf W K S, K⁆ := hYU hy
      rw [← hmap] at h1
      obtain ⟨u, hu, hu'⟩ := h1
      have : u = y := Subtype.ext hu'
      exact this ▸ hu
    have hY'inv : ∀ g ∈ khOf hR, ∀ y ∈ Y.subgroupOf (vOf W K S),
        g y ∈ Y.subgroupOf (vOf W K S) := by
      intro g hg y hy
      obtain ⟨k, rfl⟩ := (mem_khOf_iff hR g).1 hg
      exact hYinv k k.2 y hy
    rcases hs.irred _ hY'le hY'inv with hb | ht
    · left
      refine eq_bot_iff.2 fun y hy => ?_
      have hyV : y ∈ vOf W K S := hle (hYU hy)
      have h1 : (⟨y, hyV⟩ : ↥(vOf W K S)) ∈ Y.subgroupOf (vOf W K S) := hy
      rw [hb] at h1
      have h2 := Subgroup.mem_bot.1 h1
      exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)
    · right
      refine le_antisymm hYU fun x hx => ?_
      rw [← hmap] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      rw [← ht] at hu
      exact hu
  · intro z hz v hv
    have hzK : z ∈ K := hz.1
    have hc := kToKh_mem_center_of_zPre hR (k := ⟨z, hzK⟩) hz
    rw [hs.center, Subgroup.mem_bot] at hc
    have := (kToKh_eq_one_iff hR ⟨z, hzK⟩).1 hc v hv
    calc z * v * z⁻¹ = (v * z) * z⁻¹ := by rw [this]
      _ = v := by group

end A7

section Root
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem bar_perfect (h : Setup28 W K S) : commutator ↥(bar W K) = ⊤ := by
  haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 h.hK.2.1
  haveI : Group.IsPerfect ↥(bar W K) := Group.IsPerfect.ofSurjective (toBar_props W K).1
  exact Group.IsPerfect.commutator_eq_top

theorem rootFour_of_card_aux (h : Setup28 W K S) {n : ℕ}
    {e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))}
    (hact : ActsLikeSubRootFourCQ (bar W S) (bar W K) n e)
    (hge : 4 ≤ Nat.card ↥(indAut W K S)) : ActsLikeRootFourCQ (bar W S) (bar W K) n e := by
  obtain ⟨V₄, Vs, hV₄, hle, hcq⟩ := hact
  have hperf : commutator ↥(bar W K) = ⊤ := bar_perfect h
  have key : ∀ φ : ↥(indAut W K S), ∃ v : ↥Vs,
      InducesOn e (φ : MulAut ↥(bar W K)) (MulAut.conj (v : ↥(alternatingGroup (Fin n)))) := by
    intro φ
    obtain ⟨σ, hσ, hind⟩ := hcq.1 φ φ.2
    obtain ⟨v, hv, rfl⟩ := hσ
    exact ⟨⟨v, hv⟩, hind⟩
  choose f hf using key
  have hinj : Function.Injective f := by
    intro φ₁ φ₂ h12
    apply Subtype.ext
    have hφ : (φ₁ : MulAut ↥(bar W K)) * (φ₂ : MulAut ↥(bar W K))⁻¹ = 1 := by
      refine aut_eq_one_of_trivial_modZ' hperf (le_refl _) _ fun x => ?_
      set y : ↥(bar W K) := (φ₂ : MulAut ↥(bar W K))⁻¹ x with hy
      have hx : x = (φ₂ : MulAut ↥(bar W K)) y := by rw [hy]; simp
      have h1 := hf φ₁ y
      have h2 := hf φ₂ y
      rw [h12] at h1
      have h3 : (QuotientGroup.mk ((φ₁ : MulAut ↥(bar W K)) y) : ↥(bar W K) ⧸ Subgroup.center _) =
          QuotientGroup.mk ((φ₂ : MulAut ↥(bar W K)) y) := e.injective (h1.trans h2.symm)
      have h4 := QuotientGroup.eq.1 h3.symm
      have h5 : ((φ₁ : MulAut ↥(bar W K)) * (φ₂ : MulAut ↥(bar W K))⁻¹) x =
          (φ₁ : MulAut ↥(bar W K)) y := by rw [hy]; simp
      rw [h5, hx]
      exact h4
    exact mul_inv_eq_one.1 hφ
  have hcard : Nat.card ↥(indAut W K S) ≤ Nat.card ↥Vs := Nat.card_le_card_of_injective f hinj
  have hVs4 : Nat.card ↥Vs ≤ 4 := by
    rw [← hV₄.1]; exact Subgroup.card_le_of_le hle
  have hVs : Vs = V₄ := Subgroup.eq_of_le_of_card_ge hle (by rw [hV₄.1]; omega)
  exact ⟨V₄, hV₄, hVs ▸ hcq⟩

end Root

section CardInd
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem card_indAut_eq (h : Setup28 W K S) {A : Subgroup X} (hAS : A ≤ S) :
    Nat.card ↥(indAut W K A) = (kerAct W K S).relIndex A := by
  have hAN : A ≤ Subgroup.normalizer (K : Set X) := hAS.trans h.hN
  let g : ↥A →* MulAut ↥(bar W K) :=
    (bar W K).normalizerMonoidHom.comp
      (((QuotientGroup.mk' W).comp A.subtype).codRestrict _
        (fun a => mk_mem_normalizer_bar' (hAN a.2)))
  have hrange : indAut W K A = g.range := by
    ext φ
    constructor
    · rintro ⟨⟨y, hyN⟩, hy, rfl⟩
      obtain ⟨a, haA, hay⟩ := Subgroup.mem_subgroupOf.1 hy
      exact ⟨⟨a, haA⟩, congrArg (bar W K).normalizerMonoidHom (Subtype.ext hay)⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨QuotientGroup.mk' W a, mk_mem_normalizer_bar' (hAN a.2)⟩,
        Subgroup.mem_subgroupOf.2 ⟨a, a.2, rfl⟩, rfl⟩
  have hker : g.ker = (kerAct W K S).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : g a = indOf W (hAN a.2) := rfl
    rw [h1, indOf_eq_one_iff]
    exact ⟨fun hb => ⟨hAS a.2, hb⟩, fun hb => hb.2⟩
  rw [hrange, ← Subgroup.index_ker, hker]
  rfl

end CardInd

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.Hyp3Aux

