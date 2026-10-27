module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools
public import CFSG.GH74.GLS.Stage2.OddAut.BTCanon
public import CFSG.GH74.GLS.Stage2.OddAut.PFix

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Subgroup CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Defs

variable {Y : Type} [Group Y]

@[expose] def stabR (A : Subgroup (MulAut Y)) (R : Subgroup Y) : Subgroup (MulAut Y) where
  carrier := {α | α ∈ A ∧ R.map α.toMonoidHom = R}
  one_mem' := ⟨A.one_mem, by
    have : (1 : MulAut Y).toMonoidHom = MonoidHom.id Y := rfl
    rw [this, Subgroup.map_id]⟩
  mul_mem' {α β} hα hβ := ⟨A.mul_mem hα.1 hβ.1, by
    have e : (α * β).toMonoidHom = α.toMonoidHom.comp β.toMonoidHom := MonoidHom.ext fun x => rfl
    rw [e, ← Subgroup.map_map, hβ.2, hα.2]⟩
  inv_mem' {α} hα := ⟨A.inv_mem hα.1, by
    have h := congrArg (Subgroup.map α⁻¹.toMonoidHom) hα.2
    have e : α⁻¹.toMonoidHom.comp α.toMonoidHom = MonoidHom.id Y :=
      MonoidHom.ext fun x => MulAut.inv_apply_self Y α x
    rw [Subgroup.map_map, e, Subgroup.map_id] at h
    exact h.symm⟩

variable (Y) in
@[expose] def ParCharP (p : ℕ) (A : Subgroup (MulAut Y)) : Prop :=
  ∀ R : Subgroup Y, R ≠ ⊥ → IsPGroup p R →
    CFSG.Open.pCoreOf p (Subgroup.normalizer (R : Set Y)) = R →
    Subgroup.normalizer (R : Set Y) ≠ ⊤ →
    (∃ S : Sylow p Y, Subgroup.normalizer ((S : Subgroup Y) : Set Y) ≤
      Subgroup.normalizer (R : Set Y)) →
    ∀ G : Subgroup (MulAut Y), G ≤ A → R.map (MulAut.conj : Y →* MulAut Y) ≤ G →
      (∀ α ∈ G, R.map α.toMonoidHom = R) → IsCharacteristicP p ↥G

end Defs

section Main

theorem exists_mul_of_mem_sup_comm {M : Type*} [Group M] {H K : Subgroup M}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : M} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let S : Subgroup M :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨h, hh, k, hk, rfl⟩ ⟨h', hh', k', hk', rfl⟩
        refine ⟨h * h', H.mul_mem hh hh', k * k', K.mul_mem hk hk', ?_⟩
        calc h * k * (h' * k') = h * (k * h') * k' := by group
          _ = h * (h' * k) * k' := by rw [← hc h' hh' k hk]
          _ = h * h' * (k * k') := by group
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        rw [mul_inv_rev]
        exact (hc _ (H.inv_mem hh) _ (K.inv_mem hk)).symm }
  have hH : H ≤ S := fun h hh => ⟨h, hh, 1, K.one_mem, by simp⟩
  have hK : K ≤ S := fun k hk => ⟨1, H.one_mem, k, hk, by simp⟩
  exact (sup_le hH hK) hx

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]

omit [Finite Y] in
theorem normal_range_conj : ((MulAut.conj : Y →* MulAut Y).range).Normal := by
  refine ⟨fun x ⟨a, ha⟩ φ => ⟨φ a, ?_⟩⟩
  rw [← ha]
  exact (mulAut_conj_conj φ a).symm

omit [Finite Y] [Fact p.Prime] in
theorem map_radInf_zpowers {y : Y} (α : MulAut Y) (hα : α y = y) :
    (radInf p (Subgroup.zpowers y)).map α.toMonoidHom = radInf p (Subgroup.zpowers y) := by
  apply radInf_map_eq (p := p) α
  have h : α.toMonoidHom y = y := hα
  rw [MonoidHom.map_zpowers, h]

theorem false_of_rp {A : Subgroup (MulAut Y)} (hBT : Holds Y p) (hcen : Subgroup.center Y = ⊥)
    (hpc : ParCharP Y p A) (hInnA : (MulAut.conj : Y →* MulAut Y).range ≤ A)
    {V Z : Subgroup (MulAut Y)} (hVA : V ≤ A) (hZA : Z ≤ A)
    (h2 : N2Cfg Y p V Z) (h3 : N3Full Y V Z)
    (hin : ∃ v ∈ V, v ≠ 1 ∧ v ∈ (MulAut.conj : Y →* MulAut Y).range) : False := by
  obtain ⟨-, -, hVe, -, hZab, -, hZcop, hZbot, hcomm⟩ := h2
  obtain ⟨v, hvV, hv1, ⟨y, rfl⟩⟩ := hin
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    mulAut_conj_injective_of_center_bot hcen
  have := hVe
  have hvp : (MulAut.conj y) ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian _ hvV
  have hyp : y ^ p = 1 := by
    apply hinj
    rw [map_pow, hvp, map_one]
  have hy1 : y ≠ 1 := fun h => hv1 (by rw [h, map_one])
  have hord : orderOf y = p := orderOf_eq_prime hyp hy1
  have hR0p : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hR0 : Subgroup.zpowers y ≠ ⊥ := by
    intro h
    apply hy1
    have : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
    rw [h, Subgroup.mem_bot] at this
    exact this
  obtain ⟨hR0le, hRp, -, hNne, hcore, hSyl⟩ := canonical_parabolic hBT hR0 hR0p
  set R : Subgroup Y := radInf p (Subgroup.zpowers y) with hR
  have hRne : R ≠ ⊥ := fun h => hR0 (le_bot_iff.1 (hR0le.trans h.le))
  have hyR : y ∈ R := hR0le (Subgroup.mem_zpowers y)
  have hfix : ∀ α : MulAut Y, α * MulAut.conj y = MulAut.conj y * α → α y = y := by
    intro α hα
    apply hinj
    have := mulAut_conj_conj α y
    rw [← this, hα]
    group
  have hVcomm : ∀ a ∈ V, a * MulAut.conj y = MulAut.conj y * a := fun a ha =>
    setLike_mul_comm ha hvV
  have hZcomm : ∀ b ∈ Z, b * MulAut.conj y = MulAut.conj y * b := fun b hb =>
    (hcomm _ hvV b hb).symm
  set A₁ : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range ⊔ (V ⊔ Z) with hA₁
  set G : Subgroup (MulAut Y) := stabR A₁ R with hG
  have hVZc : ∀ a ∈ V, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => (hcomm a ha b hb)
  have hVG : ∀ a ∈ V, a ∈ G := fun a ha =>
    ⟨Subgroup.mem_sup_right (Subgroup.mem_sup_left ha),
      map_radInf_zpowers a (hfix a (hVcomm a ha))⟩
  have hZG : ∀ b ∈ Z, b ∈ G := fun b hb =>
    ⟨Subgroup.mem_sup_right (Subgroup.mem_sup_right hb),
      map_radInf_zpowers b (hfix b (hZcomm b hb))⟩
  have hZGle : Z ≤ G := fun b hb => hZG b hb
  have hA₁A : A₁ ≤ A := sup_le hInnA (sup_le hVA hZA)
  have hGA : G ≤ A := fun α hα => hA₁A hα.1
  have hconjG : R.map (MulAut.conj : Y →* MulAut Y) ≤ G := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨Subgroup.mem_sup_left ⟨r, rfl⟩, ?_⟩
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      show r * z * r⁻¹ ∈ R
      exact R.mul_mem (R.mul_mem hr hz) (R.inv_mem hr)
    · intro hx
      refine ⟨r⁻¹ * x * r, R.mul_mem (R.mul_mem (R.inv_mem hr) hx) hr, ?_⟩
      show r * (r⁻¹ * x * r) * r⁻¹ = x
      group
  have hchar : IsCharacteristicP p ↥G :=
    hpc R hRne hRp hcore hNne hSyl G hGA hconjG (fun α hα => hα.2)
  have := normal_range_conj (Y := Y)
  set Rhat : Subgroup ↥G := (R.map (MulAut.conj : Y →* MulAut Y)).subgroupOf G with hRhat
  have hRhatN : Rhat.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨r, hr, hrx⟩ := (Subgroup.mem_subgroupOf.1 hx)
    have hg : R.map (g : MulAut Y).toMonoidHom = R := g.2.2
    have hgr : (g : MulAut Y) r ∈ R := by
      rw [← hg]
      exact Subgroup.mem_map_of_mem _ hr
    refine Subgroup.mem_subgroupOf.2 ⟨(g : MulAut Y) r, hgr, ?_⟩
    have := mulAut_conj_conj (g : MulAut Y) r
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hrx]
    simpa using this.symm
  have hRhatP : IsPGroup p Rhat :=
    (hRp.map _).of_equiv (Subgroup.subgroupOfEquivOfLe hconjG).symm
  have hvG : MulAut.conj y ∈ G := hconjG ⟨y, hyR, rfl⟩
  set v' : ↥G := ⟨MulAut.conj y, hvG⟩ with hv'
  have hv'Q : v' ∈ CFSG.pCore p ↥G :=
    le_sSup (show Rhat ∈ {K : Subgroup ↥G | K.Normal ∧ IsPGroup p K} from ⟨hRhatN, hRhatP⟩)
      (show v' ∈ Rhat from Subgroup.mem_subgroupOf.2 ⟨y, hyR, rfl⟩)
  have hQp : IsPGroup p (CFSG.pCore p ↥G) := CFSG.pCore_isPGroup (p := p) (G := ↥G)
  have hQn : (CFSG.pCore p ↥G).Normal := CFSG.pCore_normal (p := p) (G := ↥G)
  have hW : Z.subgroupOf G = ⊥ := by
    refine oPrime_centralizer_eq_bot (G := ↥G) (p := p) (Q := CFSG.pCore p ↥G) hQp hQn hchar hv'Q
      ?_ ?_ ?_
    · intro w hw
      apply Subtype.ext
      exact hZcomm (w : MulAut Y) (Subgroup.mem_subgroupOf.1 hw)
    · intro c hc w hw
      have hc' : (c : MulAut Y) * MulAut.conj y = MulAut.conj y * (c : MulAut Y) :=
        congrArg Subtype.val hc
      have hwZ : (w : MulAut Y) ∈ Z := Subgroup.mem_subgroupOf.1 hw
      obtain ⟨ιu, ⟨u, rfl⟩, x, hx, hcx⟩ := Subgroup.mem_sup_of_normal_left.1 c.2.1
      obtain ⟨a, ha, b, hb, hxab⟩ := exists_mul_of_mem_sup_comm hVZc hx
      have hab : (a * b) * MulAut.conj y = MulAut.conj y * (a * b) := by
        calc (a * b) * MulAut.conj y = a * (b * MulAut.conj y) := by group
          _ = a * (MulAut.conj y * b) := by rw [hZcomm b hb]
          _ = (a * MulAut.conj y) * b := by group
          _ = (MulAut.conj y * a) * b := by rw [hVcomm a ha]
          _ = MulAut.conj y * (a * b) := by group
      have hcomm' : MulAut.conj u * MulAut.conj y = MulAut.conj y * MulAut.conj u := by
        have h1 : (MulAut.conj u * (a * b)) * MulAut.conj y =
            MulAut.conj y * (MulAut.conj u * (a * b)) := by
          rw [← hxab, hcx]; exact hc'
        have h2 : (MulAut.conj u * MulAut.conj y) * (a * b) =
            (MulAut.conj y * MulAut.conj u) * (a * b) := by
          calc (MulAut.conj u * MulAut.conj y) * (a * b)
              = MulAut.conj u * (MulAut.conj y * (a * b)) := by group
            _ = MulAut.conj u * ((a * b) * MulAut.conj y) := by rw [hab]
            _ = (MulAut.conj u * (a * b)) * MulAut.conj y := by group
            _ = MulAut.conj y * (MulAut.conj u * (a * b)) := h1
            _ = (MulAut.conj y * MulAut.conj u) * (a * b) := by group
        exact mul_right_cancel h2
      have huy : u * y = y * u := by
        apply hinj
        rw [map_mul, map_mul]
        exact hcomm'
      have hufix : u ∈ fixSub (MulAut.conj y) := by
        rw [mem_fixSub, MulAut.conj_apply]
        calc y * u * y⁻¹ = (y * u) * y⁻¹ := rfl
          _ = (u * y) * y⁻¹ := by rw [huy]
          _ = u := by group
      have hnorm := h3 (MulAut.conj y) hvV hv1 u hufix
      have hwab : (a * b) * (w : MulAut Y) = (w : MulAut Y) * (a * b) := by
        calc (a * b) * (w : MulAut Y) = a * (b * (w : MulAut Y)) := by group
          _ = a * ((w : MulAut Y) * b) := by rw [hZab b hb w hwZ]
          _ = (a * (w : MulAut Y)) * b := by group
          _ = ((w : MulAut Y) * a) * b := by rw [hcomm a ha w hwZ]
          _ = (w : MulAut Y) * (a * b) := by group
      refine Subgroup.mem_subgroupOf.2 ?_
      have hcoe : ((c * w * c⁻¹ : ↥G) : MulAut Y) =
          MulAut.conj u * (w : MulAut Y) * (MulAut.conj u)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hcx, hxab]
        calc MulAut.conj u * (a * b) * (w : MulAut Y) * (MulAut.conj u * (a * b))⁻¹
            = MulAut.conj u * ((a * b) * (w : MulAut Y)) * (a * b)⁻¹ * (MulAut.conj u)⁻¹ := by
              group
          _ = MulAut.conj u * ((w : MulAut Y) * (a * b)) * (a * b)⁻¹ * (MulAut.conj u)⁻¹ := by
              rw [hwab]
          _ = MulAut.conj u * (w : MulAut Y) * (MulAut.conj u)⁻¹ := by group
      rw [hcoe]
      exact (Subgroup.mem_normalizer_iff.1 hnorm _).1 hwZ
    · have hcard : Nat.card ↥(Z.subgroupOf G) = Nat.card ↥Z :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZGle).toEquiv
      rw [hcard]
      exact hZcop
  apply hZbot
  rw [eq_bot_iff]
  intro z hz
  have h1 : (⟨z, hZG z hz⟩ : ↥G) ∈ Z.subgroupOf G := Subgroup.mem_subgroupOf.2 hz
  rw [hW, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h1

end Main

end CFSG.GH74.GLS.Stage2.OddAut
