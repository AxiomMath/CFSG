module

public import CFSG.GH74.GLS.Stage4.T6Cent
public import CFSG.Adapters.Involutions
public import CFSG.GH74.GLS.Stage4.T6Steps

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem oddCore_odd' (Q : Type) [Group Q] [Finite Q] : Odd (Nat.card ↥(CFSG.oddCore Q)) := by
  by_contra hev
  have h2 : 2 ∣ Nat.card ↥(CFSG.oddCore Q) := by
    rw [Nat.not_odd_iff_even] at hev
    exact even_iff_two_dvd.1 hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(CFSG.oddCore Q)) 2 h2
  exact CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two (t := (x : Q)) (by rwa [Subgroup.orderOf_coe])
    x.2

theorem oddCore_map_le (Q : Type) [Group Q] [Finite Q] (α : Q ≃* Q) :
    (CFSG.oddCore Q).map α.toMonoidHom ≤ CFSG.oddCore Q := by
  have hn : ((CFSG.oddCore Q).map α.toMonoidHom).Normal :=
    (inferInstance : (CFSG.oddCore Q).Normal).map α.toMonoidHom α.surjective
  have hodd : Odd (Nat.card ↥((CFSG.oddCore Q).map α.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective α.injective]
    exact oddCore_odd' Q
  exact le_sSup ⟨hn, hodd⟩

variable {N : T2N3 G} {u : G} {p : ℕ}

abbrev C₂ (N : T2N3 G) : Subgroup G := Subgroup.centralizer (N.X₂ : Set G)

noncomputable abbrev Wsub (N : T2N3 G) : Subgroup G := (CFSG.oddCore ↥(C₂ N)).map (C₂ N).subtype

theorem K₁_le_C₂ (h : T6Ctx N u p) : N.K₁ ≤ C₂ N := by
  intro k hk
  refine Subgroup.mem_centralizer_iff.2 (fun x hx => ?_)
  have := K₁_cent_X₂ h hk hx
  calc x * k = (k * x * k⁻¹) * k := by rw [this]
    _ = k * x := by group

theorem C₂_le_M₂ : C₂ N ≤ M₂ N := by
  intro c hc
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have h1 := Subgroup.mem_centralizer_iff.1 hc x hx
  have : c * x * c⁻¹ = x := by
    calc c * x * c⁻¹ = (x * c) * c⁻¹ := by rw [h1]
      _ = x := by group
  rw [this]; exact hx

omit [Finite G] in
theorem M₂_norm_C₂ {m : G} (hm : m ∈ M₂ N) {c : G} (hc : c ∈ C₂ N) : m * c * m⁻¹ ∈ C₂ N := by
  refine Subgroup.mem_centralizer_iff.2 (fun x hx => ?_)
  have hm' : m⁻¹ * x * m ∈ N.X₂ := by
    have := (Subgroup.mem_normalizer_iff.1 ((M₂ N).inv_mem hm) x).1 hx
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 hc _ hm'
  calc x * (m * c * m⁻¹) = m * ((m⁻¹ * x * m) * c) * m⁻¹ := by group
    _ = m * (c * (m⁻¹ * x * m)) * m⁻¹ := by rw [h1]
    _ = (m * c * m⁻¹) * x := by group

theorem Wsub_norm {m : G} (hm : m ∈ M₂ N) {w : G} (hw : w ∈ Wsub N) : m * w * m⁻¹ ∈ Wsub N := by
  obtain ⟨o, ho, rfl⟩ := hw
  let σ : ↥(C₂ N) ≃* ↥(C₂ N) :=
    { toFun := fun c => ⟨m * c * m⁻¹, M₂_norm_C₂ hm c.2⟩
      invFun := fun c => ⟨m⁻¹ * c * m, by simpa using M₂_norm_C₂ ((M₂ N).inv_mem hm) c.2⟩
      left_inv := fun c => Subtype.ext (by show m⁻¹ * (m * (c : G) * m⁻¹) * m = c; group)
      right_inv := fun c => Subtype.ext (by show m * (m⁻¹ * (c : G) * m) * m⁻¹ = c; group)
      map_mul' := fun a b => by apply Subtype.ext; simp [mul_assoc] }
  have h1 := oddCore_map_le ↥(C₂ N) σ
  have : σ o ∈ (CFSG.oddCore ↥(C₂ N)).map σ.toMonoidHom := ⟨o, ho, rfl⟩
  exact ⟨σ o, h1 this, rfl⟩

theorem Wsub_odd {w : G} (hw : w ∈ Wsub N) : Odd (orderOf w) := by
  obtain ⟨o, ho, rfl⟩ := hw
  have := CFSG.Adapters.odd_orderOf_of_mem_oddCore (m := o) ho
  rwa [← Subgroup.orderOf_coe o] at this

theorem X₂_le_W (h : T6Ctx N u p) : N.X₂ ≤ Wsub N := by
  intro x hx
  have hxC : x ∈ C₂ N := Subgroup.mem_centralizer_iff.2 (fun y hy => h.sec5.loc.X₂_comm y hy x hx)
  have hX₂C : N.X₂ ≤ C₂ N := fun y hy => Subgroup.mem_centralizer_iff.2
    (fun y' hy' => h.sec5.loc.X₂_comm y' hy' y hy)
  let X' : Subgroup ↥(C₂ N) := N.X₂.subgroupOf (C₂ N)
  have hX'n : X'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := Subgroup.mem_centralizer_iff.1 g.2 (n : G) hn
    have h2 : (g : G) * n * (g : G)⁻¹ = n := by
      calc (g : G) * n * (g : G)⁻¹ = (n * g) * (g : G)⁻¹ := by rw [this]
        _ = n := by group
    simpa [h2] using hn⟩
  have hX'odd : Odd (Nat.card ↥X') := by
    have : Nat.card ↥X' = Nat.card ↥N.X₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₂C).toEquiv
    rw [this, h.sec5.loc.card_X₂]
    exact h.sec5.loc.q₂_odd
  have hle : X' ≤ CFSG.oddCore ↥(C₂ N) := le_sSup ⟨hX'n, hX'odd⟩
  exact ⟨⟨x, hxC⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem Zstar_C₂ (h : T6Ctx N u p) :
    ∀ c ∈ C₂ N, ∃ c' ∈ C₂ N, ∃ k ∈ Wsub N, c = c' * k ∧ c' * N.z = N.z * c' := by
  have hloc := h.sec5.loc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 := h.ctx.zz
  have hzK₁ := hloc.z_mem_K₁
  have hzC₂ : N.z ∈ C₂ N := K₁_le_C₂ h hzK₁
  have hK₁C₂ := K₁_le_C₂ h
  obtain ⟨S₁⟩ : Nonempty (Sylow 2 ↥N.K₁) := inferInstance
  set T₁ : Subgroup G := (S₁ : Subgroup ↥N.K₁).map N.K₁.subtype with hT₁
  have hT₁K : T₁ ≤ N.K₁ := Subgroup.map_subtype_le _
  have hT₁p : IsPGroup 2 ↥T₁ := S₁.isPGroup'.map _
  have hT₁idx : ¬ 2 ∣ T₁.relIndex N.K₁ := by
    have : T₁.relIndex N.K₁ = (S₁ : Subgroup ↥N.K₁).index := by
      unfold Subgroup.relIndex
      rw [hT₁]
      show (Subgroup.comap N.K₁.subtype (Subgroup.map N.K₁.subtype (S₁ : Subgroup ↥N.K₁))).index = _
      rw [Subgroup.comap_map_eq_self_of_injective N.K₁.subtype_injective]
    rw [this]
    exact S₁.not_dvd_index
  have hzT : N.z ∈ T₁ := by
    let Z' : Subgroup ↥N.K₁ := (Subgroup.zpowers N.z).subgroupOf N.K₁
    have hZn : Z'.Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hn
      have hc : (g : G) * N.z = N.z * (g : G) := h.ctx.C.zc₁ g g.2
      have : (g : G) * (n : G) * (g : G)⁻¹ = n := by
        rw [← hj]
        have hcomm : Commute (g : G) (N.z ^ j) := (Commute.zpow_right (Commute.eq hc |> fun e => e) j)
        rw [hcomm.eq]; group
      rw [show ((g * n * g⁻¹ : ↥N.K₁) : G) = (g : G) * n * (g : G)⁻¹ from rfl, this]
      exact hn⟩
    have hZp : IsPGroup 2 ↥Z' := by
      have : IsPGroup 2 ↥(Subgroup.zpowers N.z) := by
        intro g
        refine ⟨1, ?_⟩
        apply Subtype.ext
        rcases t2C_zpowers_cases hz2 g.2 with h1 | h1
        · simp [h1]
        · simp [h1, pow_two, hz2]
      exact this.comap_subtype
    have := hZp.le_sylow_of_normal S₁ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers N.z) :
      (⟨N.z, hzK₁⟩ : ↥N.K₁) ∈ Z')
    exact ⟨⟨N.z, hzK₁⟩, this, rfl⟩
  let T₁' : Subgroup ↥(C₂ N) := T₁.subgroupOf (C₂ N)
  have hT₁'p : IsPGroup 2 ↥T₁' := hT₁p.comap_subtype
  obtain ⟨Q, hQ⟩ := hT₁'p.exists_le_sylow
  set E : Subgroup G := (Q : Subgroup ↥(C₂ N)).map (C₂ N).subtype with hE
  have hEp : IsPGroup 2 ↥E := Q.isPGroup'.map _
  have hEC : ∀ e ∈ E, ∀ x ∈ N.X₂, e * x * e⁻¹ = x := by
    rintro e ⟨q, -, rfl⟩ x hx
    have := Subgroup.mem_centralizer_iff.1 q.2 x hx
    show (q : G) * x * (q : G)⁻¹ = x
    calc (q : G) * x * (q : G)⁻¹ = (x * q) * (q : G)⁻¹ := by rw [this]
      _ = x := by group
  have hTE : T₁ ≤ E := by
    intro t ht
    exact ⟨⟨t, hK₁C₂ (hT₁K ht)⟩, hQ (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hET := Sylow2_C₂ h hT₁K hT₁p hT₁idx hzT hEp hEC hTE
  have hQT : ∀ q : ↥(C₂ N), q ∈ (Q : Subgroup ↥(C₂ N)) → (q : G) ∈ T₁ := by
    intro q hq
    rw [← hET]
    exact ⟨q, hq, rfl⟩
  have hzQ : (⟨N.z, hzC₂⟩ : ↥(C₂ N)) ∈ (Q : Subgroup ↥(C₂ N)) :=
    hQ (Subgroup.mem_subgroupOf.2 hzT)
  let z' : ↥(Q : Subgroup ↥(C₂ N)) := ⟨⟨N.z, hzC₂⟩, hzQ⟩
  have hzZ : z' ∈ Subgroup.center ↥(Q : Subgroup ↥(C₂ N)) := by
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    apply Subtype.ext
    show (q : G) * N.z = N.z * (q : G)
    exact h.ctx.C.zc₁ _ (hT₁K (hQT q.1 q.2))
  have hz'ord : orderOf z' = 2 := by
    have h1 : orderOf (z' : ↥(C₂ N)) = orderOf (z' : ↥(C₂ N)) := rfl
    rw [← Subgroup.orderOf_coe z', ← Subgroup.orderOf_coe (z' : ↥(C₂ N))]
    exact hloc.z_ord
  have hwc : ∀ g : ↥(C₂ N), g⁻¹ * (z' : ↥(C₂ N)) * g ∈ (Q : Subgroup ↥(C₂ N)) →
      g⁻¹ * (z' : ↥(C₂ N)) * g = (z' : ↥(C₂ N)) := by
    intro g hg
    have hK : ((g⁻¹ * (z' : ↥(C₂ N)) * g : ↥(C₂ N)) : G) ∈ N.K₁ := hT₁K (hQT _ hg)
    have hsq : ((g⁻¹ * (z' : ↥(C₂ N)) * g : ↥(C₂ N)) : G) * ((g⁻¹ * (z' : ↥(C₂ N)) * g : ↥(C₂ N)) : G) = 1 := by
      show (g : G)⁻¹ * N.z * g * ((g : G)⁻¹ * N.z * g) = 1
      calc (g : G)⁻¹ * N.z * g * ((g : G)⁻¹ * N.z * g) = (g : G)⁻¹ * (N.z * N.z) * g := by group
        _ = 1 := by rw [hz2]; group
    have hne : ((g⁻¹ * (z' : ↥(C₂ N)) * g : ↥(C₂ N)) : G) ≠ 1 := by
      intro h1
      apply h.ctx.z_ne
      have : (g : G)⁻¹ * N.z * g = 1 := h1
      calc N.z = (g : G) * ((g : G)⁻¹ * N.z * g) * (g : G)⁻¹ := by group
        _ = 1 := by rw [this]; group
    apply Subtype.ext
    rcases h.inv₁ _ hK hsq with h1 | h1
    · exact absurd h1 hne
    · exact h1
  obtain ⟨hdec, -⟩ := CFSG.Adapters.glauberman_zStar Q z' hzZ hz'ord hwc
  intro c hc
  obtain ⟨c'', hc'', k, hk, hck⟩ := hdec ⟨c, hc⟩
  refine ⟨(c'' : G), c''.2, (k : G), ⟨k, hk, rfl⟩, ?_, ?_⟩
  · have := congrArg Subtype.val hck
    simpa using this
  · have := Subgroup.mem_centralizer_singleton_iff.1 hc''
    have := congrArg Subtype.val this
    simpa using this

omit [Finite G] in
theorem mem_of_sq_mem {W : Subgroup G} {r : G} (hodd : Odd (orderOf r)) (h : r * r ∈ W) : r ∈ W := by
  obtain ⟨k, hk⟩ := hodd
  have h1 : r ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one r
  have h2 : r = (r * r) ^ (k + 1) := by
    have : (r * r) ^ (k + 1) = r ^ (2 * k + 1) * r := by
      rw [← pow_two, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ]
    rw [this, h1, one_mul]
  rw [h2]
  exact Subgroup.pow_mem _ h _

theorem R_le_W (h : T6Ctx N u p) {y : G} {R : Subgroup G} (hTS : T6TSdata N p y R) : R ≤ Wsub N := by
  intro r hr
  have hrC₂ : r ∈ C₂ N := hTS.R_cent hr
  obtain ⟨c', hc'C, k, hk, hrck, hc'z⟩ := Zstar_C₂ h r hrC₂
  have hzM := z_mem_M₂ h
  have hc'M : c' ∈ M₂ N := C₂_le_M₂ hc'C
  have hk₂ : N.z * k * N.z⁻¹ ∈ Wsub N := Wsub_norm hzM hk
  have hk₃ : c' * (N.z * k * N.z⁻¹) * c'⁻¹ ∈ Wsub N := Wsub_norm hc'M hk₂
  have hx : N.z * r * N.z⁻¹ * r ∈ Wsub N := X₂_le_W h (hTS.R_inv r hr)
  have hzc' : N.z * c' * N.z⁻¹ = c' := by
    calc N.z * c' * N.z⁻¹ = (c' * N.z) * N.z⁻¹ := by rw [hc'z]
      _ = c' := by group
  have hzr : N.z * r * N.z⁻¹ = c' * (N.z * k * N.z⁻¹) := by
    rw [hrck]
    calc N.z * (c' * k) * N.z⁻¹ = (N.z * c' * N.z⁻¹) * (N.z * k * N.z⁻¹) := by group
      _ = c' * (N.z * k * N.z⁻¹) := by rw [hzc']
  have hcc : c' * c' ∈ Wsub N := by
    have e : c' * c' = (c' * (N.z * k * N.z⁻¹) * c'⁻¹)⁻¹ * (N.z * r * N.z⁻¹ * r) * k⁻¹ := by
      rw [hzr, hrck]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hk₃) hx) (Subgroup.inv_mem _ hk)
  have hk₄ : c'⁻¹ * k * c' ∈ Wsub N := by
    have := Wsub_norm ((M₂ N).inv_mem hc'M) hk
    simpa using this
  have hrr : r * r ∈ Wsub N := by
    have e : r * r = (c' * c') * (c'⁻¹ * k * c') * k := by rw [hrck]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcc hk₄) hk
  exact mem_of_sq_mem (t6_odd_of_pGroup h.prime h.p_ne_two hTS.R_p hr) hrr

omit [Finite G] in
theorem Wsub_le_C₂ : Wsub N ≤ C₂ N := by
  rintro _ ⟨o, -, rfl⟩
  exact o.2

theorem Wsub_card_odd : Odd (Nat.card ↥(Wsub N)) := by
  rw [Subgroup.card_map_of_injective (C₂ N).subtype_injective]
  exact oddCore_odd' _

theorem Wsub_inf_K₁ (h : T6Ctx N u p) : Wsub N ⊓ N.K₁ = ⊥ := by
  have hz2 : ¬ Odd (orderOf N.z) := by
    rw [h.sec5.loc.z_ord]; decide
  have hQ := h.ctx.C.Q₁ (Wsub N ⊓ N.K₁) inf_le_right (fun k hk n hn => by
    refine ⟨Wsub_norm (K₁_le_M₂ h hk) hn.1, ?_⟩
    exact N.K₁.mul_mem (N.K₁.mul_mem hk hn.2) (N.K₁.inv_mem hk))
  rcases hQ with hle | hle
  · rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rcases t2C_zpowers_cases h.ctx.zz (hle hx) with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ Wsub_odd hx.1) hz2
  · exact absurd (Wsub_odd (hle h.sec5.loc.z_mem_K₁).1) hz2

theorem W_Cz (h : T6Ctx N u p) : ∀ y ∈ Wsub N, N.z * y * N.z⁻¹ = y → y ∈ N.X₂ :=
  Cz_gen h (X₂_le_W h) (fun _ hy => Wsub_odd hy)
    (fun _ hk _ hy => Wsub_norm (K₁_le_M₂ h hk) hy) (Wsub_inf_K₁ h)
    (fun y hy x hx => by
      have := Subgroup.mem_centralizer_iff.1 (Wsub_le_C₂ hy) x hx
      calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [this]
        _ = x := by group)

theorem W_comm (h : T6Ctx N u p) : ∀ r ∈ Wsub N, ∀ s ∈ Wsub N, ⁅r, s⁆ ∈ N.X₂ := by
  refine (t6_inv_mod (R := Wsub N) (X := N.X₂) ?_ Wsub_card_odd h.sec5.loc.z_ord ?_ (W_Cz h)).2
  · intro x hx r hr
    exact Subgroup.mem_centralizer_iff.1 (Wsub_le_C₂ hr) x hx
  · exact Subgroup.mem_normalizer_fintype (fun n hn => Wsub_norm (z_mem_M₂ h) hn)

theorem W_nilp (h : T6Ctx N u p) : Group.IsNilpotent ↥(Wsub N) := by
  refine ⟨⟨2, ?_⟩⟩
  rw [eq_top_iff]
  intro x _
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro y
  rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have hc : ⁅(x : G), (y : G)⁆ ∈ N.X₂ := W_comm h x x.2 y y.2
  have := Subgroup.mem_centralizer_iff.1 (Wsub_le_C₂ g.2) _ hc
  exact this.symm

theorem R_le_R₂ (h : T6Ctx N u p) {y : G} {R : Subgroup G} (hTS : T6TSdata N p y R) : R ≤ R₂ N p := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hnil := W_nilp h
  have hRW : R ≤ Wsub N := R_le_W h hTS
  have hRp : IsPGroup p ↥(R.subgroupOf (Wsub N)) :=
    hTS.R_p.of_equiv (Subgroup.subgroupOfEquivOfLe hRW).symm
  obtain ⟨S, hRS⟩ := hRp.exists_le_sylow
  have hSn : (S : Subgroup ↥(Wsub N)).Normal := Group.IsNilpotent.sylow_normal hnil p S
  have hSc : (S : Subgroup ↥(Wsub N)).Characteristic := Sylow.characteristic_of_normal S hSn
  set P : Subgroup G := (S : Subgroup ↥(Wsub N)).map (Wsub N).subtype with hP
  have hPnorm : Subgroup.normalizer (Wsub N : Set G) ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hMW : M₂ N ≤ Subgroup.normalizer (Wsub N : Set G) := fun m hm =>
    Subgroup.mem_normalizer_fintype (fun w hw => Wsub_norm hm hw)
  have hPW : P ≤ Wsub N := Subgroup.map_subtype_le _
  have hPM : P ≤ M₂ N := hPW.trans (Wsub_le_C₂.trans C₂_le_M₂)
  have hPp : IsPGroup p ↥P := S.isPGroup'.map _
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p hPM (hMW.trans hPnorm) hPp
  intro r hr
  exact hle ⟨⟨r, hRW hr⟩, hRS (Subgroup.mem_subgroupOf.2 hr), rfl⟩

theorem t6_Rle : T6RleProp := by
  intro G _ _ N u p h y R hTS
  exact R_le_R₂ h hTS

end CFSG.GH74.GLS.Stage4.Rest.T6
