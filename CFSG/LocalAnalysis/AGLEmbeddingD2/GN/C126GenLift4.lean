module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenLift2
import CFSG.Quasithin.Background.C126A5Comm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenModule
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 Equiv
  CFSG.LieType.BorelTits

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N : ℕ}

@[expose] def cq (A Q W : Subgroup G) (hAW : ∀ a ∈ A, ∀ w ∈ W, a * w * a⁻¹ ∈ W) : Subgroup G where
  carrier := {k | k ∈ A ∧ ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ W}
  one_mem' := ⟨A.one_mem, fun q _ => by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, fun q hq => by
    have h1 := hAW a ha.1 _ (hb.2 q hq)
    have h2 := ha.2 q hq
    have : a * b * q * (a * b)⁻¹ * q⁻¹ =
        (a * (b * q * b⁻¹ * q⁻¹) * a⁻¹) * (a * q * a⁻¹ * q⁻¹) := by group
    rw [this]; exact W.mul_mem h1 h2⟩
  inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, fun q hq => by
    have h2 := ha.2 q hq
    have h3 : a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ = a⁻¹ * (a * q * a⁻¹ * q⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [h3]; exact hAW a⁻¹ (A.inv_mem ha.1) _ (W.inv_mem h2)⟩

omit [Finite G] in
theorem conj_mem_cq {A Q W : Subgroup G} {hAW : ∀ a ∈ A, ∀ w ∈ W, a * w * a⁻¹ ∈ W}
    (hAQ : ∀ a ∈ A, ∀ q ∈ Q, a * q * a⁻¹ ∈ Q) {a z : G} (ha : a ∈ A)
    (hz : z ∈ cq A Q W hAW) : a * z * a⁻¹ ∈ cq A Q W hAW := by
  refine ⟨A.mul_mem (A.mul_mem ha hz.1) (A.inv_mem ha), fun q hq => ?_⟩
  have h1 := hz.2 (a⁻¹ * q * a) (by simpa using hAQ a⁻¹ (A.inv_mem ha) q hq)
  have := hAW a ha _ h1
  have e : a * z * a⁻¹ * q * (a * z * a⁻¹)⁻¹ * q⁻¹ =
      a * (z * (a⁻¹ * q * a) * z⁻¹ * (a⁻¹ * q * a)⁻¹) * a⁻¹ := by group
  rw [e]; exact this

@[expose] def valHom {V : Subgroup G} (hV : IsElemAbelian 2 V) : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := rfl
  map_mul' := fun _ _ => rfl

namespace SymLift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : GenSetting H T M V Y hV}
  {d : GenData N H T V Y hV}

variable (d) in
@[expose] def Vc : Subgroup G := (commV d.L).map (valHom hV)

omit [Finite G] in
theorem mem_Vc {u : G} : u ∈ Vc d ↔ ∃ w ∈ commV d.L, w.val = u := by
  unfold Vc; simp [valHom, Subgroup.mem_map]; rfl

omit [Finite G] in
theorem Vc_le_V : Vc d ≤ V := by
  rintro u hu
  obtain ⟨w, -, rfl⟩ := mem_Vc.1 hu
  exact w.val_mem

omit [Finite G] in
theorem Vc_conj {a u : G} (ha : a ∈ A₁ s d) (hu : u ∈ Vc d) : a * u * a⁻¹ ∈ Vc d := by
  obtain ⟨w, hw, rfl⟩ := mem_Vc.1 hu
  obtain ⟨haH, haL⟩ := mem_A₁.1 ha
  refine mem_Vc.2 ⟨cv hV a w, act_mem_commV' haL hw, cv_val hV (s.H_le_N haH) w⟩

omit [Finite G] in
theorem Vc_hAW : ∀ a ∈ A₁ s d, ∀ w ∈ Vc d, a * w * a⁻¹ ∈ Vc d := fun _ ha _ hw =>
  Vc_conj ha hw

variable (s d) in
@[expose] def cqK : Subgroup G := cq (A₁ s d) (pCoreOf 2 H) (Vc d) (Vc_hAW (s := s) (d := d))

omit [Finite G] in
theorem mem_cqK {k : G} : k ∈ cqK s d ↔ k ∈ A₁ s d ∧ ∀ q ∈ pCoreOf 2 H, k * q * k⁻¹ * q⁻¹ ∈ Vc d :=
  Iff.rfl

omit [Finite G] in
theorem A₁_normalizes_Q : ∀ a ∈ A₁ s d, ∀ q ∈ pCoreOf 2 H, a * q * a⁻¹ ∈ pCoreOf 2 H :=
  fun _ ha q hq => (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H (A₁_le_H ha)) q).1 hq

namespace XData

variable {x : G} (hx : XData s d x)

include hx

theorem four_comm_V : 4 ≤ {c : G | ∃ v ∈ V, c = x * v * x⁻¹ * v⁻¹}.ncard := by
  have h := four_commutators d.θ d.β d.hβ d.hN d.hab d.hbp d.hap (h := (⟨cv hV x, hx.mem_L⟩ : ↥d.L))
    (by rw [← d.th_of_mem hx.mem_L]; exact hx.th_eq)
  set R := Set.range fun w : ↥(commV d.L) =>
    (((⟨cv hV x, hx.mem_L⟩ : ↥d.L) : MulAut (IntMod V hV)) (w : IntMod V hV)) *
      (w : IntMod V hV)⁻¹ with hR
  have hsub : IntMod.val '' R ⊆ {c : G | ∃ v ∈ V, c = x * v * x⁻¹ * v⁻¹} := by
    rintro _ ⟨r, ⟨w, rfl⟩, rfl⟩
    refine ⟨(w : IntMod V hV).val, (w : IntMod V hV).val_mem, ?_⟩
    rw [IntMod.val_mul, IntMod.val_inv]
    simp only
    rw [cv_val hV (s.H_le_N (s.Y_le hx.mem))]
  calc 4 ≤ R.ncard := h
    _ = (IntMod.val '' R).ncard := (Set.ncard_image_of_injective R IntMod.val_injective).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

variable (hY : IsShort2 Y) (hA3 : IsAltType Y 3)

include hY hA3

theorem comm_mem_V (q : G) (hq : q ∈ pCoreOf 2 H) :
    ∃ v ∈ V, x * q * x⁻¹ * q⁻¹ = x * v * x⁻¹ * v⁻¹ := by
  refine CFSG.Quasithin.C126.A5.exists_comm_V hY hA3 hx.mem hx.ord ?_ ?_ ?_ ?_ ?_ hx.four_comm_V q
    hq
  · intro q hq y hy
    exact (Subgroup.mem_normalizer_iff.1 (s.Q_norm hq) y).1 hy
  · intro y hy q hq
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H (s.Y_le hy)) q).1 hq
  · intro q hq
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨q, hq⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  · intro c hcY hcQ
    have hn : Y ≤ Subgroup.normalizer ((Y ⊓ pCoreOf 2 H : Subgroup G) : Set G) := fun y hy =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hy, le_normalizer_pCoreOf 2 H (s.Y_le hy)⟩
    exact le_pCoreOf_of_le_normalizer 2 inf_le_left hn
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right) ⟨hcY, hcQ⟩
  · exact (MinParabolic.le_pCoreOf_of_isTwoReduced s.red)

theorem x_mem_cq : x ∈ cqK s d := by
  refine ⟨hx.x_mem_A₁, fun q hq => ?_⟩
  obtain ⟨v, hv, hqv⟩ := hx.comm_mem_V hY hA3 q hq
  rw [hqv]
  refine mem_Vc.2 ⟨cv hV x (IntMod.mk hV ⟨v, hv⟩) * (IntMod.mk hV ⟨v, hv⟩)⁻¹,
    mem_commV_gen' hx.mem_L _, ?_⟩
  rw [IntMod.val_mul, IntMod.val_inv, cv_val hV (s.H_le_N (s.Y_le hx.mem))]
  rfl

theorem Khat_le_cq : Khat s d x ≤ cqK s d := by
  unfold Khat
  refine conjClosure_le fun a ha z hz => ?_
  have hxz : Subgroup.zpowers x ≤ cqK s d := by
    rw [Subgroup.zpowers_le]; exact hx.x_mem_cq hY hA3
  exact conj_mem_cq (A₁_normalizes_Q (s := s) (d := d)) ha (hxz hz)

end XData

end SymLift

omit [Finite G] in
theorem eq_one_of_pow_three {c : G} (h3 : c ^ 3 = 1) {k : ℕ} (hk : c ^ 2 ^ k = 1) : c = 1 := by
  have h1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hg : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  have := Nat.dvd_gcd h1 h2
  rw [hg] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

namespace SymLift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : GenSetting H T M V Y hV}
  {d : GenData N H T V Y hV}

namespace XData

variable {x : G} (hx : XData s d x)

include hx

omit [Finite G] in
theorem coversAlt : CoversAlt d.θ (autI hV (Khat s d x)) := by
  intro g hg
  have hg' := hg
  rw [← normalClosure_c3 d.hab d.hbp d.hap] at hg'
  have hKN : Khat s d x ≤ Subgroup.normalizer (V : Set G) := hx.Khat_le_H.trans s.H_le_N
  let F := autI hV (Khat s d x)
  let Sg : Subgroup (Perm (Fin N)) := ((F ⊓ d.L).subgroupOf d.L).map d.θ.toMonoidHom
  have hconj : ∀ u : Perm (Fin N), u * c3 d.a d.b d.p * u⁻¹ ∈ Sg := by
    intro u
    obtain ⟨φ, hφ, hφu⟩ := d.exists_of_th (g := u)
    obtain ⟨a, ha, hav⟩ := exists_A₁_cv (s := s) (d := d) hφ
    have haH : a ∈ H := (mem_A₁.1 ha).1
    have hk : a * x * a⁻¹ ∈ Khat s d x :=
      mem_conjClosure ha (Subgroup.mem_zpowers x)
    have hkcv : cv hV (a * x * a⁻¹) = φ * cv hV x * φ⁻¹ := by
      rw [cv_mul hV (Subgroup.mul_mem _ (s.H_le_N haH) (s.H_le_N (s.Y_le hx.mem)))
        (s.H_le_N (H.inv_mem haH)), cv_mul hV (s.H_le_N haH) (s.H_le_N (s.Y_le hx.mem)),
        cv_inv hV (s.H_le_N haH), hav]
    have hkL : cv hV (a * x * a⁻¹) ∈ d.L := by
      rw [hkcv]; exact d.L.mul_mem (d.L.mul_mem hφ hx.mem_L) (d.L.inv_mem hφ)
    have hkF : cv hV (a * x * a⁻¹) ∈ F := (mem_autI_iff hV hKN).2 ⟨_, hk, rfl⟩
    refine ⟨⟨cv hV (a * x * a⁻¹), hkL⟩, Subgroup.mem_subgroupOf.2 ⟨hkF, hkL⟩, ?_⟩
    show d.θ ⟨cv hV (a * x * a⁻¹), hkL⟩ = _
    rw [← d.th_of_mem hkL, hkcv, d.th_mul (d.L.mul_mem hφ hx.mem_L) (d.L.inv_mem hφ),
      d.th_mul hφ hx.mem_L, d.th_inv hφ, hφu, hx.th_eq]
  have hle : Subgroup.normalClosure {c3 d.a d.b d.p} ≤ Sg := by
    unfold Subgroup.normalClosure
    rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨b, hb, hyb⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    rw [Set.mem_singleton_iff] at hb
    subst hb
    obtain ⟨u, hu⟩ := isConj_iff.1 hyb
    rw [← hu]
    exact hconj u
  obtain ⟨h, hh, hθ⟩ := hle hg'
  exact ⟨h, (Subgroup.mem_subgroupOf.1 hh).1, hθ⟩

omit [Finite G] in
theorem irred_Vc {W₀ : Subgroup G} (hW : W₀ ≤ Vc d)
    (hN : Khat s d x ≤ Subgroup.normalizer (W₀ : Set G)) : W₀ = ⊥ ∨ W₀ = Vc d := by
  have hKN : Khat s d x ≤ Subgroup.normalizer (V : Set G) := hx.Khat_le_H.trans s.H_le_N
  set U' : Subgroup (IntMod V hV) := W₀.comap (valHom hV) with hU'
  have hU'le : U' ≤ commV d.L := by
    intro w hw
    obtain ⟨w', hw', hww⟩ := mem_Vc.1 (hW hw)
    have : w' = w := IntMod.val_injective hww
    exact this ▸ hw'
  have hinv : ∀ h ∈ autI hV (Khat s d x), ∀ u ∈ U', h u ∈ U' := by
    intro h hh u hu
    obtain ⟨k, hk, rfl⟩ := (mem_autI_iff hV hKN).1 hh
    show valHom hV (cv hV k u) ∈ W₀
    show (cv hV k u).val ∈ W₀
    rw [cv_val hV (hKN hk)]
    exact (Subgroup.mem_normalizer_iff.1 (hN hk) u.val).1 hu
  rcases irred_commV d.θ d.β d.hβ d.hN d.hodd hx.coversAlt hU'le hinv with hbot | htop
  · left
    refine le_antisymm (fun u hu => ?_) bot_le
    obtain ⟨w, hw, rfl⟩ := mem_Vc.1 (hW hu)
    have : w ∈ U' := hu
    rw [hbot, Subgroup.mem_bot] at this
    rw [this]; exact (Subgroup.mem_bot.2 rfl)
  · right
    refine le_antisymm hW (fun u hu => ?_)
    obtain ⟨w, hw, rfl⟩ := mem_Vc.1 hu
    have : w ∈ U' := htop ▸ hw
    exact this

variable (hY : IsShort2 Y) (hA3 : IsAltType Y 3)

include hY hA3

theorem blockU_le_Vc : blockU (Khat s d x) ≤ Vc d := by
  unfold blockU blockQ
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have haQ : a ∈ pCoreOf 2 H := (hx.pCoreOf_Khat ▸ ha).2
  have := (mem_cqK.1 (hx.Khat_le_cq hY hA3 hb)).2 a haQ
  have e : ⁅a, b⁆ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  rw [e]
  exact (Vc d).inv_mem this

omit hY hA3 in
theorem blockU_ne_bot : blockU (Khat s d x) ≠ ⊥ := by
  intro hbot
  obtain ⟨c, ⟨v, hv, hcv⟩, hc1⟩ : ∃ c ∈ {c : G | ∃ v ∈ V, c = x * v * x⁻¹ * v⁻¹}, c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : {c : G | ∃ v ∈ V, c = x * v * x⁻¹ * v⁻¹} ⊆ {1} := fun c hc => hcon c hc
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := hx.four_comm_V
    rw [Set.ncard_singleton] at h1
    omega
  have hvQ : v ∈ pCoreOf 2 H := MinParabolic.le_pCoreOf_of_isTwoReduced s.red hv
  have hvA : v ∈ A₁ s d := Q_le_A₁ hvQ
  have hxK : x ∈ Khat s d x := zpowers_le_Khat s d x (Subgroup.mem_zpowers x)
  have hcK : c ∈ Khat s d x := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (A₁_le_normalizer_Khat s d x hvA) x⁻¹).1
      ((Khat s d x).inv_mem hxK)
    have := (Khat s d x).mul_mem hxK h1
    rw [hcv]
    simpa [mul_assoc] using this
  have hxH : x ∈ H := s.Y_le hx.mem
  have hcQ : c ∈ pCoreOf 2 H := by
    have h1 : x * v * x⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H hxH) v).1 hvQ
    rw [hcv]
    exact (pCoreOf 2 H).mul_mem h1 ((pCoreOf 2 H).inv_mem hvQ)
  have hcO : c ∈ blockQ (Khat s d x) := by
    show _ ∈ pCoreOf 2 (Khat s d x)
    rw [hx.pCoreOf_Khat]; exact ⟨hcK, hcQ⟩
  have hU : c * x * c⁻¹ * x⁻¹ ∈ blockU (Khat s d x) := C1.commutator_mem_blockU hcO hxK
  rw [hbot, Subgroup.mem_bot] at hU
  have h2 : c * x * c⁻¹ = x := mul_inv_eq_one.1 hU
  have h3 : c * x = x * c := by
    have := congrArg (· * c) h2
    simpa [mul_assoc] using this
  have hcomm : x * c * x⁻¹ = c := by
    calc x * c * x⁻¹ = c * x * x⁻¹ := by rw [h3]
      _ = c := by group
  have hnorm := CFSG.Quasithin.C126.A5.norm_comm_eq_one (x := x) (q := v)
    (by rw [← hx.ord]; exact pow_orderOf_eq_one x)
  rw [← hcv] at hnorm
  simp only [hcomm] at hnorm
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨c, hcQ⟩
  exact hc1 (eq_one_of_pow_three (by simpa [pow_succ, mul_assoc] using hnorm)
    (congrArg Subtype.val hk))

theorem blockU_eq_Vc : blockU (Khat s d x) = Vc d := by
  have hle := hx.blockU_le_Vc hY hA3
  rcases hx.irred_Vc hle (C1.le_normalizer_blockU _) with h | h
  · exact absurd h hx.blockU_ne_bot
  · exact h

theorem blockZ_eq_bot : blockZ (Khat s d x) = ⊥ := by
  refine le_antisymm (fun u hu => ?_) bot_le
  have hKN : Khat s d x ≤ Subgroup.normalizer (V : Set G) := hx.Khat_le_H.trans s.H_le_N
  have huV : u ∈ Vc d := hx.blockU_eq_Vc hY hA3 ▸ hu.1
  obtain ⟨w, hw, rfl⟩ := mem_Vc.1 huV
  have hfix : ∀ h ∈ autI hV (Khat s d x), h w = w := by
    intro h hh
    obtain ⟨k, hk, rfl⟩ := (mem_autI_iff hV hKN).1 hh
    apply IntMod.val_injective
    rw [cv_val hV (hKN hk), Subgroup.mem_centralizer_iff.1 hu.2 k hk]
    group
  have h1 := fix_commV d.θ d.β d.hβ d.hN d.hodd hx.coversAlt hw hfix
  rw [h1]
  exact Subgroup.one_mem _

end XData

end SymLift

end CFSG.AGLEmbeddingD2.GN
