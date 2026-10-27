module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatData

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

section Group

theorem le_of_overgroup_dichotomy {Γ : Type*} [Group Γ] (L D D0 U E Mm : Subgroup Γ)
    (hDE : D ≤ E) (hEL : E ≤ L ⊔ D) (hDn : D ≤ Subgroup.normalizer (L : Set Γ))
    (hD : D = U ⊔ D0) (hUL : U ≤ L) (hcomm : ∀ l ∈ L, ∀ d ∈ D0, l * d = d * l)
    (hover : ∀ Y : Subgroup Γ, Y ≤ L → U ≤ Y →
      (∃ y ∈ Y, y ∉ Subgroup.normalizer (U : Set Γ)) → Y = L)
    (hM : ∀ φ ∈ E, φ ∈ Subgroup.normalizer (D : Set Γ) → φ ∈ Mm) (hnot : ¬ E ≤ Mm) :
    L ≤ E := by
  by_contra hLE
  have hUE : U ≤ E := by
    have : U ≤ D := by rw [hD]; exact le_sup_left
    exact this.trans hDE
  have hZ : ∀ y ∈ E ⊓ L, y ∈ Subgroup.normalizer (U : Set Γ) := by
    intro y hy
    by_contra hyn
    have h1 := hover (E ⊓ L) inf_le_right (le_inf hUE hUL) ⟨y, hy, hyn⟩
    exact hLE (h1 ▸ inf_le_left)
  apply hnot
  intro φ hφ
  apply hM φ hφ
  have hφ' : φ ∈ ((L ⊔ D : Subgroup Γ) : Set Γ) := hEL hφ
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L D hDn] at hφ'
  obtain ⟨l, hl, d, hd, rfl⟩ := hφ'
  have hlE : l ∈ E := by
    have : l = (l * d) * d⁻¹ := by group
    rw [this]
    exact E.mul_mem hφ (E.inv_mem (hDE hd))
  have hlN : l ∈ Subgroup.normalizer (U : Set Γ) := hZ l ⟨hlE, hl⟩
  have h0 : l ∈ Subgroup.normalizer (D0 : Set Γ) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    exact Subgroup.mem_centralizer_iff.2 fun x hx => (hcomm l hl x hx).symm
  have hlD : l ∈ Subgroup.normalizer (D : Set Γ) := by
    rw [hD]
    exact Subgroup.inf_normalizer_le_normalizer_sup U D0 ⟨hlN, h0⟩
  exact (Subgroup.normalizer (D : Set Γ)).mul_mem hlD (Subgroup.le_normalizer hd)

end Group

section Rho

variable {G : Type} [Group G] {V : Subgroup G}

theorem autOn_sup_eq [V.Normal] (A B : Subgroup G) :
    autOn (A ⊔ B) V = autOn A V ⊔ autOn B V := by
  rw [autOn_eq_map_conjNormal, autOn_eq_map_conjNormal, autOn_eq_map_conjNormal, Subgroup.map_sup]

theorem le_of_autOn_le [V.Normal] {P M : Subgroup G}
    (hker : Subgroup.centralizer (V : Set G) ≤ M) (h : autOn P V ≤ autOn M V) : P ≤ M := by
  intro x hx
  have hρx : MulAut.conjNormal (H := V) x ∈ autOn M V := by
    apply h
    rw [autOn_eq_map_conjNormal]
    exact Subgroup.mem_map_of_mem _ hx
  rw [autOn_eq_map_conjNormal] at hρx
  obtain ⟨m, hm, hmx⟩ := hρx
  have hk : m⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
    rw [← conjNormal_eq_one_iff, map_mul, map_inv, hmx, inv_mul_cancel]
  have hx' : x = m * (m⁻¹ * x) := by group
  rw [hx']
  exact M.mul_mem hm (hker hk)

theorem apply_mem_modComm {A : Subgroup (MulAut V)} {a : MulAut V} (ha : a ∈ A) {w : V}
    (hw : (w : G) ∈ modComm V A) : ((a w : V) : G) ∈ modComm V A := by
  have h1 : ((a w : V) : G) * (w : G)⁻¹ ∈ modComm V A := Subgroup.subset_closure ⟨a, ha, w, rfl⟩
  have h2 : ((a w : V) : G) = (((a w : V) : G) * (w : G)⁻¹) * (w : G) := by group
  rw [h2]
  exact Subgroup.mul_mem _ h1 hw

@[expose] def pointwiseFixer (V I : Subgroup G) : Subgroup (MulAut V) where
  carrier := {x | ∀ w : V, (w : G) ∈ I → x w = w}
  one_mem' := fun w _ => rfl
  mul_mem' := by
    intro x y hx hy w hw
    rw [MulAut.mul_apply, hy w hw, hx w hw]
  inv_mem' := by
    intro x hx w hw
    calc x⁻¹ w = x⁻¹ (x w) := by rw [hx w hw]
      _ = w := by simp

end Rho

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem natI_isTwoReducedIn {R M V P : Subgroup G} [V.Normal] {r : ℕ}
    {Lc : Fin r → Subgroup (MulAut V)} (hVe : IsElemAbelian 2 V) (hdata : NatFamilyData R M V Lc)
    (i : Fin r) (hIP : modComm V (Lc i) ≤ P) (hEL : autOn P V ≤ Lc i ⊔ autOn (baum R) V)
    (hLE : Lc i ≤ autOn P V) : IsTwoReducedIn P (modComm V (Lc i)) := by
  classical
  have hnormV : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (V : Set G) := fun A x _ => by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  have hIV : modComm V (Lc i) ≤ V := modComm_le V (Lc i)
  have hEn : autOn P V ≤ Subgroup.normalizer (Lc i : Set (MulAut V)) :=
    hEL.trans (sup_le Subgroup.le_normalizer (hdata.normS i))
  have hPn : P ≤ Subgroup.normalizer ((modComm V (Lc i) : Subgroup G) : Set G) :=
    le_normalizer_modComm hEn
  have hIe : IsElemAbelian 2 (modComm V (Lc i)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hVe.2 x (hIV hx)⟩
    have h0 := hVe.1.is_comm.comm (⟨a, hIV a.2⟩ : ↥V) ⟨b, hIV b.2⟩
    have h2 : (a : G) * b = (b : G) * a := congrArg Subtype.val h0
    exact Subtype.ext h2
  refine ⟨hIP, hPn, hIe, ?_⟩
  intro D'' hD''P hPD'' hD''k
  set L := Lc i with hLdef
  set D := autOn (baum R) V with hDdef
  set I := modComm V L with hIdef
  set Nn := autOn D'' V with hNn
  have hNE : Nn ≤ autOn P V := autOn_le_autOn V hD''P
  have hENn : autOn P V ≤ Subgroup.normalizer (Nn : Set (MulAut V)) :=
    autOn_le_normalizer_autOn (hnormV _) (hnormV _) hPD''
  have hIinv : ∀ κ ∈ L, ∀ w : V, (w : G) ∈ I → ((κ w : V) : G) ∈ I :=
    fun κ hκ w hw => apply_mem_modComm hκ hw
  have hN3p : ∀ n ∈ Nn ⊓ L, ∃ k : ℕ, n ^ (2 ^ k) = 1 := by
    rintro n ⟨hnN, hnL⟩
    rw [hNn, autOn_eq_map_conjNormal] at hnN
    obtain ⟨d, hd, rfl⟩ := hnN
    obtain ⟨k, hk⟩ := hD''k d hd
    refine ⟨k, ?_⟩
    refine hdata.faithful i _ (pow_mem hnL _) ?_
    intro u hu
    rw [← map_pow]
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have h1 := Subgroup.mem_centralizer_iff.1 hk (u : G) hu
    rw [← h1]
    group
  have hN3le : Nn ⊓ L ≤ pCoreOf 2 L := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      exact le_normalizer_inf_of_le (hLE.trans hENn) Subgroup.le_normalizer
    · intro x
      obtain ⟨k, hk⟩ := hN3p x.1 x.2
      exact ⟨k, Subtype.ext hk⟩
  have hN3 : Nn ⊓ L = ⊥ := le_bot_iff.1 (hN3le.trans (hdata.O2 i).le)
  intro d hd
  set φ := MulAut.conjNormal (H := V) d with hφ
  have hφN : φ ∈ Nn := by
    rw [hNn, autOn_eq_map_conjNormal]
    exact Subgroup.mem_map_of_mem _ hd
  have hφE : φ ∈ autOn P V := hNE hφN
  have hφcomm : ∀ κ ∈ L, φ * κ = κ * φ := by
    intro κ hκ
    have hκn : κ ∈ Subgroup.normalizer (Nn : Set (MulAut V)) := hENn (hLE hκ)
    have hφn : φ ∈ Subgroup.normalizer (L : Set (MulAut V)) := hEn hφE
    have h1 : φ * κ * φ⁻¹ * κ⁻¹ ∈ Nn ⊓ L := by
      refine ⟨?_, ?_⟩
      · have h2 : κ * φ⁻¹ * κ⁻¹ ∈ Nn := (Subgroup.mem_normalizer_iff.1 hκn _).1 (Nn.inv_mem hφN)
        have h3 := Nn.mul_mem hφN h2
        have : φ * (κ * φ⁻¹ * κ⁻¹) = φ * κ * φ⁻¹ * κ⁻¹ := by group
        rwa [this] at h3
      · exact L.mul_mem ((Subgroup.mem_normalizer_iff.1 hφn κ).1 hκ) (L.inv_mem hκ)
    rw [hN3, Subgroup.mem_bot] at h1
    calc φ * κ = (φ * κ * φ⁻¹ * κ⁻¹) * (κ * φ) := by group
      _ = κ * φ := by rw [h1, one_mul]
  set U := autOn R V ⊓ L with hU
  set D0 := ⨆ j, ⨆ (_ : j ≠ i), autOn R V ⊓ Lc j with hD0
  have hsplit : D = U ⊔ D0 := by
    rw [hDdef, hdata.decomp]
    exact iSup_split_single (fun j => autOn R V ⊓ Lc j) i
  have hD0c : D0 ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
    refine iSup₂_le fun j hj => ?_
    intro y hy
    exact Subgroup.mem_centralizer_iff.2 fun x hx =>
      hdata.commute i j (Ne.symm hj) x hx y hy.2
  have hD0fix : D0 ≤ pointwiseFixer V I := by
    refine iSup₂_le fun j hj => ?_
    intro y hy w hw
    exact hdata.others i j hj y hy.2 w hw
  have hUD0 : D0 ≤ Subgroup.normalizer (U : Set (MulAut V)) := by
    intro y hy
    have hyc : y ∈ Subgroup.centralizer (L : Set (MulAut V)) := hD0c hy
    refine Subgroup.centralizer_le_normalizer _ ?_
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    exact Subgroup.mem_centralizer_iff.1 hyc x hx.2
  have hDn : D ≤ Subgroup.normalizer (L : Set (MulAut V)) := hdata.normS i
  have hφLD : φ ∈ L ⊔ D := hEL hφE
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left L D hDn] at hφLD
  obtain ⟨l, hl, u, hu, hlu⟩ := hφLD
  have hu' : u ∈ ((U ⊔ D0 : Subgroup (MulAut V)) : Set (MulAut V)) := by rw [← hsplit]; exact hu
  rw [Subgroup.coe_mul_of_right_le_normalizer_left U D0 hUD0] at hu'
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := hu'
  have hu₁L : u₁ ∈ L := hu₁.2
  set lam := l * u₁ with hlam
  have hlamL : lam ∈ L := L.mul_mem hl hu₁L
  have hφ_eq : φ = lam * u₂ := by rw [← hlu, hlam]; group
  have hφI : ∀ w : V, (w : G) ∈ I → φ w = lam w := by
    intro w hw
    rw [hφ_eq, MulAut.mul_apply, hD0fix hu₂ w hw]
  have hlamc : ∀ κ ∈ L, ∀ w : V, (w : G) ∈ I → lam (κ w) = κ (lam w) := by
    intro κ hκ w hw
    have h1 : φ (κ w) = κ (φ w) := by
      have := congrArg (fun ξ : MulAut V => ξ w) (hφcomm κ hκ)
      simpa [MulAut.mul_apply] using this
    rw [hφI (κ w) (hIinv κ hκ w hw), hφI w hw] at h1
    exact h1
  have hlamz : ∀ κ ∈ L, κ * lam = lam * κ := by
    intro κ hκ
    have hc : lam * κ * lam⁻¹ * κ⁻¹ = 1 := by
      refine hdata.faithful i _ (L.mul_mem (L.mul_mem (L.mul_mem hlamL hκ) (L.inv_mem hlamL))
        (L.inv_mem hκ)) ?_
      intro u hu
      have hwI : ((lam⁻¹ (κ⁻¹ u) : V) : G) ∈ I :=
        hIinv lam⁻¹ (L.inv_mem hlamL) _ (hIinv κ⁻¹ (L.inv_mem hκ) u hu)
      have h3 := hlamc κ hκ (lam⁻¹ (κ⁻¹ u)) hwI
      have h4 : (lam * κ * lam⁻¹ * κ⁻¹) u = lam (κ (lam⁻¹ (κ⁻¹ u))) := by
        simp [MulAut.mul_apply]
      rw [h4, h3]
      simp
    calc κ * lam = (lam * κ * lam⁻¹ * κ⁻¹)⁻¹ * (lam * κ) := by group
      _ = lam * κ := by rw [hc]; group
  have hlam1 : lam = 1 := hdata.center i lam hlamL hlamz
  refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
  have hwV : (w : G) ∈ V := hIV hw
  have h1 : φ ⟨w, hwV⟩ = ⟨w, hwV⟩ := by
    rw [hφI ⟨w, hwV⟩ hw, hlam1]
    rfl
  have h2 := congrArg (fun v : V => (v : G)) h1
  simp only [hφ, MulAut.conjNormal_apply] at h2
  calc w * d = (d * w * d⁻¹) * d := by rw [h2]
    _ = d * w := by group

theorem natMinPImageProp
    : NatMinPImageProp := by
  intro G _ _ R M V n F _ r Lc ctx i P hbase hY hmin hbasic
  classical
  have hS := ctx.setting
  have hX := ctx.hX
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hdata := nat_family_data hS ctx.comps ctx.natural
  have hbridge := even_SL2_original_bridge hS ctx.comps
  have hker : Subgroup.centralizer (V : Set G) ≤ M := fun x hx =>
    hbridge.C0_le_M ⟨Subgroup.mem_top x, hx⟩
  set D := autOn (baum R) V with hDdef
  have hρT0 : autOn (oddOrderSubgroup (rhoPreimage V ⊤ hX (Lc i)) ⊔ baum R) V = Lc i ⊔ D := by
    rw [autOn_sup_eq, hY.image]
  have hDE : D ≤ autOn P V := autOn_le_autOn V hmin.S_le
  have hEL : autOn P V ≤ Lc i ⊔ D := (autOn_le_autOn V hmin.le).trans hρT0.le
  have hsplit : D = (autOn R V ⊓ Lc i) ⊔ ⨆ j, ⨆ (_ : j ≠ i), autOn R V ⊓ Lc j := by
    rw [hDdef, hdata.decomp]
    exact iSup_split_single (fun j => autOn R V ⊓ Lc j) i
  have hD0comm : ∀ l ∈ Lc i, ∀ d ∈ (⨆ j, ⨆ (_ : j ≠ i), autOn R V ⊓ Lc j), l * d = d * l := by
    intro l hl d hd
    have hle : (⨆ j, ⨆ (_ : j ≠ i), autOn R V ⊓ Lc j) ≤
        Subgroup.centralizer (Lc i : Set (MulAut V)) := by
      refine iSup₂_le fun j hj => ?_
      intro y hy
      exact Subgroup.mem_centralizer_iff.2 fun x hx =>
        hdata.commute i j (Ne.symm hj) x hx y hy.2
    exact Subgroup.mem_centralizer_iff.1 (hle hd) l hl
  have hM : ∀ φ ∈ autOn P V, φ ∈ Subgroup.normalizer (D : Set (MulAut V)) → φ ∈ autOn M V :=
    fun φ hφ hφn => hdata.M_ge φ (autOn_le_autOn V le_top hφ) hφn
  have hnot : ¬ autOn P V ≤ autOn M V := fun h => hmin.not_le (le_of_autOn_le hker h)
  have hLE : Lc i ≤ autOn P V :=
    le_of_overgroup_dichotomy (Lc i) D _ (autOn R V ⊓ Lc i) (autOn P V) (autOn M V) hDE hEL
      (hdata.normS i) hsplit inf_le_right hD0comm (hdata.overgroup i) hM hnot
  have hIS : modComm V (Lc i) ≤ baum R :=
    (modComm_le V (Lc i)).trans (hbase.V_le_Q.trans hbase.Q_le_S)
  refine ⟨le_antisymm hEL (sup_le hLE hDE), hIS, ?_⟩
  exact natI_isTwoReducedIn hS.reduced.2.2.1 hdata i (hIS.trans hmin.S_le) hEL hLE

end Main

end CFSG.QuasithinUnique.Setup.Lift
