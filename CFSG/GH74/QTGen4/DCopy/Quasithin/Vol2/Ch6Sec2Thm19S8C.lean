module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Thm19Inputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Thm19S8B
public import CFSG.Quasithin.EmptyFaithful.SzN28X0Main
public import CFSG.Quasithin.Vol2.Ch6Sec2Thm19B
public import CFSG.Quasithin.Vol2.Ch6Sec2Thm19S8A

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs CFSG.Quasithin CFSG.Quasithin.G11
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem false_s8_ch619_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4)
    (h512 : Stmt5_1_2_F4) (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h626 : Stmt6_2_6_F4)
    (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4)
    (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) (hZlt : zCh611 T < centerOf (uCh611 T L V)) {l : G}
    (hl : l ∈ lsCh617 T L V) (hlH : l ∉ hCh611 T) {A : Type} [AddCommGroup A]
    [Module (ZMod 2) A] [Finite A] {B : LinearMap.BilinForm (ZMod 2) A}
    {β : ↥(uCh611 T L V) →* Multiplicative A} {ρ : ↥(hCh611 T) →* (A ≃ₗ[ZMod 2] A)}
    (hR : IsSymplecticRealization (hCh611 T) (uCh611 T L V) (centerOf (uCh611 T L V)) A B β ρ)
    (h8 : G112Concl8S8 B ρ.range (((conjSubgroup (uCh611 T L V) l ⊓
      Subgroup.centralizer (ch6ZS T L V : Set G)).subgroupOf (hCh611 T)).map ρ)) : False := by
  classical
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega_F4 h331 h432 h512 h614 h615
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hZZS := h.omega_le_ZS_F4 h331 h432 h512 h614 h615
  have hUH : uCh611 T L V ≤ hCh611 T := h.uCh611_le_h_F4 h331 h432 h512 h614 h615
  have hZZU : zCh611 T ≤ centerOf (uCh611 T L V) := hZlt.le
  have hHN : hCh611 T ≤ Subgroup.normalizer (uCh611 T L V : Set G) :=
    hCh611_le_normalizer_u T L V
  have hZUN := hCh611_le_normalizer_centerOf_ch615 T L V
  have hZSU : ch6ZS T L V ≤ uCh611 T L V := le_conjClosure _ _

  obtain ⟨z', -, -, d, -, -, -, haS, haZ, -⟩ := h.gens_ch617_F4 h331 h432 h512 h614 h615
  set a := d⁻¹ * z' * d with ha
  have haU : a ∈ uCh611 T L V := hZSU haS
  have hVZU := h.inf_centerOf_eq_ch616_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have haZU : a ∉ centerOf (uCh611 T L V) := by
    intro haZU
    have : a ∈ V ⊓ centerOf (uCh611 T L V) := ⟨haS.1, haZU⟩
    rw [hVZU] at this
    exact haZ this
  obtain ⟨z₀, hz₀Z, hz₀1⟩ : ∃ z₀ ∈ zCh611 T, z₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : zCh611 T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hZ2
    omega
  have hv₁ : ∀ w : ↥(uCh611 T L V), (w : G) ∈ ch6ZS T L V →
      (w : G) ∉ centerOf (uCh611 T L V) → Multiplicative.toAdd (β w) = piA_ch619 hR a := by
    intro w hwS hwZU
    rw [← piA_eq_ch619 hR w.2]
    have hwZ : (w : G) ∉ zCh611 T := fun hwZ => hwZU (hZZU hwZ)
    rw [piA_eq_iff_ch619 hR w.2 haU]
    rcases L128P.eq_of_mem_four hZZS hZ2 hZS4 hz₀Z hz₀1 haZ haS hwS with e | e | e | e
    · exact absurd (e ▸ (zCh611 T).one_mem) hwZ
    · exact absurd (e ▸ hz₀Z) hwZ
    · rw [e, inv_mul_cancel]
      exact Subgroup.one_mem _
    · rw [e]
      have hz₀U := hZZU hz₀Z
      have hc : a * z₀ = z₀ * a := Subgroup.mem_centralizer_iff.mp hz₀U.2 a haU
      have e3 : (z₀ * a)⁻¹ * a = z₀⁻¹ := by
        calc (z₀ * a)⁻¹ * a = (a * z₀)⁻¹ * a := by rw [hc]
          _ = z₀⁻¹ := by group
      rw [e3]
      exact Subgroup.inv_mem _ hz₀U
  let Wsp : Submodule (ZMod 2) A :=
    { carrier := {x | ∃ e : ↥(uCh611 T L V),
        (e : G) ∈ uCh611 T L V ⊓ conjSubgroup (uCh611 T L V) l ∧ Multiplicative.toAdd (β e) = x}
      add_mem' := by
        rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
        exact ⟨e * e', Subgroup.mul_mem _ he he', by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, Subgroup.one_mem _, by rw [map_one, toAdd_one]⟩
      smul_mem' := by
        rintro c _ ⟨e, he, rfl⟩
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl
        · exact ⟨1, Subgroup.one_mem _, by rw [map_one, toAdd_one, zero_smul]⟩
        · exact ⟨e, he, by rw [one_smul]⟩ }
  have hW : ∀ x : A, x ∈ Wsp ↔ ∃ e : ↥(uCh611 T L V),
      (e : G) ∈ uCh611 T L V ⊓ conjSubgroup (uCh611 T L V) l ∧ Multiplicative.toAdd (β e) = x :=
    fun x => Iff.rfl

  have h111 := h.g111_ch619_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hl hlH hR hv₁ hW
  have h101 := h111.toG101Hyp
  obtain ⟨A₈, I, I', x, hS8⟩ := SzN28.s8Data_of_concl8 h101.X_le h101.X_sq h8
  have t := hS8.twoNat

  have hX0 := s8NoTrivialX0 A B ρ.range (piA_ch619 hR a) Wsp _ _ h111 h8
  obtain ⟨γ₀, hγ₀, hγ₀1⟩ : ∃ γ ∈ ((conjSubgroup (centerOf (uCh611 T L V)) l).subgroupOf
      (hCh611 T)).map ρ, γ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hX0 ((Subgroup.eq_bot_iff_forall _).mpr hcon)
  obtain ⟨⟨y, hyH⟩, hyZ, rfl⟩ := Subgroup.mem_map.mp hγ₀
  have hyZ' : y ∈ conjSubgroup (centerOf (uCh611 T L V)) l := hyZ

  obtain ⟨w, hwW, hcom⟩ := h.exists_comm_eq_ch619_F4 h331 h432 h512 h614 h615 h626 h6210 h6211
    h6212 hlt hl hlH hR hS8.exists_three hyZ' hyH hγ₀1 hz₀Z hz₀1

  have hQS : QuotSetting (hCh611 T) (uCh611 T L V) (zCh611 T) :=
    { S₂_le := hZZS.trans hZSU
      Sx_le := hUH
      nS := fun x hx y hy => (Subgroup.mem_normalizer_iff.mp (hHN hx) y).mp hy
      nS₂ := fun x hx y hy => by
        have h1 : y * x = x * y := Subgroup.mem_centralizer_iff.mp hx y hy
        have e : x * y * x⁻¹ = y := by
          calc x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [h1]
            _ = y := by group
        rw [e]
        exact hy
      abel := fun a ha b hb => h.comm_mem_ch615_F4 h331 h432 h512 h614 h615 ha hb
      sq := fun a ha => by
        have := h.sq_mem_ch615_F4 h331 h432 h512 h614 h615 ha
        rwa [pow_two] at this }
  obtain ⟨Tm⟩ := exists_tildeModel619 hQS
  have hβZ : ∀ u : ↥(uCh611 T L V), (u : G) ∈ zCh611 T → β u = 1 :=
    fun u hu => (hR.2.1 u).mpr (hZZU hu)
  have hφρ : ∀ (k : ↥(hCh611 T)) (v : Tm.V),
      Tm.phi β hβZ (Tm.ρ k v) = ρ k (Tm.phi β hβZ v) :=
    Tm.phi_ρ β hβZ ρ (fun x hx u hu => (Subgroup.mem_normalizer_iff.mp (hHN hx) u).mp hu)
      hR.2.2.1

  set P := conjClosure (conjSubgroup (centerOf (uCh611 T L V)) l) (hCh611 T) with hP
  have hZlH := h.conj_centerOf_le_ch619_F4 h331 h432 h512 h614 h615 hl
  have hPH : P ≤ hCh611 T := conjClosure_le fun k hk y' hy' =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hk (hZlH hy')) (Subgroup.inv_mem _ hk)
  have hPn : hCh611 T ≤ Subgroup.normalizer (P : Set G) := le_normalizer_conjClosure _ _
  have hPZ : P ≤ Subgroup.centralizer (centerOf (uCh611 T L V) : Set G) := by
    refine conjClosure_le fun k hk y' hy' => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : k⁻¹ * u * k ∈ centerOf (uCh611 T L V) := by
      have := (Subgroup.mem_normalizer_iff.mp (hZUN (Subgroup.inv_mem _ hk)) u).mp hu
      rwa [inv_inv] at this
    have hc := h.commute_ZU_conj_ch619_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hl
      hlH hu' hy'
    calc u * (k * y' * k⁻¹) = k * ((k⁻¹ * u * k) * y') * k⁻¹ := by group
      _ = k * (y' * (k⁻¹ * u * k)) * k⁻¹ := by rw [hc]
      _ = k * y' * k⁻¹ * u := by group
  have hyP : y ∈ P := le_conjClosure _ _ hyZ'

  set Pd := (P.subgroupOf (hCh611 T)).map ρ with hPd
  have hPdΓ : Pd ≤ ρ.range := Subgroup.map_le_range _ _
  have hPdn : ∀ γ ∈ ρ.range, ∀ n ∈ Pd, γ * n * γ⁻¹ ∈ Pd := by
    rintro _ ⟨k, rfl⟩ _ ⟨p, hp, rfl⟩
    refine ⟨k * p * k⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hPn k.2) p).mp hp
  have hPd1 : Pd ≠ ⊥ := by
    intro hbot
    have hmem : ρ ⟨y, hyH⟩ ∈ Pd := ⟨⟨y, hyH⟩, hyP, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hγ₀1 hmem
  have hAPd : A₈ ≤ Pd := hS8.A_min Pd hPdΓ hPdn hPd1

  set K : Subgroup ↥(hCh611 T) := P.subgroupOf (hCh611 T) ⊓ Subgroup.comap ρ A₈ with hK
  have hKn : K.Normal := by
    refine ⟨fun k hk g => ⟨?_, ?_⟩⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hPn g.2) (k : G)).mp hk.1
    · show ρ (g * k * g⁻¹) ∈ A₈
      rw [map_mul, map_mul, map_inv]
      exact hS8.A_normal _ ⟨g, rfl⟩ _ hk.2
  have hsA : ∀ a' ∈ A₈, ∃ k : ↥K, ρ (k : ↥(hCh611 T)) = a' := by
    intro a' ha'
    obtain ⟨p, hp, hpa⟩ := hAPd ha'
    exact ⟨⟨p, hp, show ρ p ∈ A₈ from hpa ▸ ha'⟩, hpa⟩

  have hker : ∀ k : ↥K, ρ (k : ↥(hCh611 T)) = 1 → Tm.ρ (k : ↥(hCh611 T)) = 1 := by
    intro k hk1
    have hkP : ((k : ↥(hCh611 T)) : G) ∈ P := k.2.1
    have hkC : ((k : ↥(hCh611 T)) : G) ∈
        centralizerMod (centerOf (uCh611 T L V)) (hCh611 T) (uCh611 T L V) := by
      refine mem_centralizerMod.mpr ⟨(k : ↥(hCh611 T)).2, hZUN (k : ↥(hCh611 T)).2,
        fun u hu => ?_⟩
      have hku := (Subgroup.mem_normalizer_iff.mp (hHN (k : ↥(hCh611 T)).2) u).mp hu
      have h1 := hR.2.2.1 (k : ↥(hCh611 T)) ⟨u, hu⟩ ⟨_, hku⟩ rfl
      rw [hk1] at h1
      have h2 : β (⟨_, hku⟩ * (⟨u, hu⟩ : ↥(uCh611 T L V))⁻¹) = 1 := by
        rw [map_mul, map_inv, mul_inv_eq_one]
        exact Multiplicative.toAdd.injective h1
      exact (hR.2.1 _).mp h2
    have hkZ := h.inf_centralizerMod_le_ch619_F4 h331 h432 h512 h614 h615 hPH hPn hPZ ⟨hkP, hkC⟩
    obtain ⟨-, -, hkU⟩ := mem_centralizerMod.mp hkZ
    ext v
    obtain ⟨u, rfl⟩ := Tm.c_surj v
    have hku := (Subgroup.mem_normalizer_iff.mp (hHN (k : ↥(hCh611 T)).2) u).mp u.2
    show Tm.ρ (k : ↥(hCh611 T)) (Tm.c u) = Tm.c u
    rw [Tm.ρ_c _ u hku, Tm.c_eq_iff]
    have := hkU _ (Subgroup.inv_mem _ u.2)
    simpa [mul_assoc] using this
  have hcentral : ∀ (k : ↥(hCh611 T)), (∀ u ∈ centerOf (uCh611 T L V), (k : G) * u = u * k) →
      ∀ z : Tm.V, Tm.phi β hβZ z = 0 → Tm.ρ k z = z := by
    intro k hk z hz
    obtain ⟨u, huC, rfl⟩ := (Tm.phi_eq_zero_iff β hβZ hR.2.1 z).mp hz
    have hku := (Subgroup.mem_normalizer_iff.mp (hHN k.2) u).mp u.2
    have e : (⟨(k : G) * (u : G) * (k : G)⁻¹, hku⟩ : ↥(uCh611 T L V)) = u := by
      apply Subtype.ext
      show (k : G) * (u : G) * (k : G)⁻¹ = (u : G)
      rw [hk u huC, mul_inv_cancel_right]
    rw [Tm.ρ_c k u hku, e]
  have hKZ : ∀ (k : ↥K) (z : Tm.V), Tm.phi β hβZ z = 0 →
      Tm.ρ (k : ↥(hCh611 T)) z = z := fun k =>
    hcentral _ fun u hu => (Subgroup.mem_centralizer_iff.mp (hPZ k.2.1) u hu).symm
  set Y : Subgroup ↥(hCh611 T) :=
    (conjSubgroup (centerOf (uCh611 T L V)) l).subgroupOf (hCh611 T) with hY
  have hYZ : ∀ y' ∈ Y, ∀ z : Tm.V, Tm.phi β hβZ z = 0 → Tm.ρ y' z = z := fun y' hy' =>
    hcentral _ fun u hu => (h.commute_ZU_conj_ch619_F4 h331 h432 h512 h614 h615 h626 h6210 h6211
      h6212 hlt hl hlH hu hy').symm

  have hzl : l⁻¹ * z₀ * l ∈ ch6ZS T L V := by
    have hlN : l⁻¹ ∈ Subgroup.normalizer (ch6ZS T L V : Set G) :=
      Subgroup.inv_mem _ (ls_le_ch617 hl).2
    have := (Subgroup.mem_normalizer_iff.mp hlN z₀).mp (hZZS hz₀Z)
    rwa [inv_inv] at this
  have hzlU : l⁻¹ * z₀ * l ∈ uCh611 T L V := hZSU hzl
  set vv := Tm.c ⟨l⁻¹ * z₀ * l, hzlU⟩ with hvv
  have hv : vv ∈ Submodule.span (ZMod 2)
      {x : Tm.V | ∃ y' ∈ Y, ∃ w' : Tm.V, x = Tm.ρ y' w' - w'} := by
    refine Submodule.subset_span ⟨⟨y, hyH⟩, hyZ, Tm.c ⟨w, hwW.1⟩, ?_⟩
    have hyw := (Subgroup.mem_normalizer_iff.mp (hHN hyH) w).mp hwW.1
    rw [Tm.ρ_c ⟨y, hyH⟩ ⟨w, hwW.1⟩ hyw, sub_eq_add_neg, ← Tm.c_inv, ← Tm.c_mul, hvv]
    exact congrArg Tm.c (Subtype.ext hcom.symm)
  have hzlZ : l⁻¹ * z₀ * l ∉ zCh611 T := by
    intro hz
    apply hlH
    rw [Subgroup.mem_centralizer_iff]
    intro z hz'
    rcases L128P.eq_of_mem_four hZZS hZ2 hZS4 hz₀Z hz₀1 haZ haS (hZZS hz') with e | e | e | e
    · rw [e, one_mul, mul_one]
    · have h1 : l⁻¹ * z₀ * l = z₀ := by
        rcases L128P.eq_of_mem_four hZZS hZ2 hZS4 hz₀Z hz₀1 haZ haS (hZZS hz) with e' | e' | e' | e'
        · exfalso
          apply hz₀1
          calc z₀ = l * (l⁻¹ * z₀ * l) * l⁻¹ := by group
            _ = 1 := by rw [e']; group
        · exact e'
        · exact absurd (e' ▸ hz) haZ
        · exfalso
          apply haZ
          have : a = z₀⁻¹ * (l⁻¹ * z₀ * l) := by rw [e']; group
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hz₀Z) hz
      rw [e]
      calc z₀ * l = l * (l⁻¹ * z₀ * l) := by group
        _ = l * z₀ := by rw [h1]
    · exact absurd (e ▸ hz') haZ
    · exfalso
      apply haZ
      have : a = z₀⁻¹ * z := by rw [e]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hz₀Z) hz'
  have hgen : Submodule.span (ZMod 2) (Set.range fun θ : ↥(hCh611 T) => Tm.ρ θ vv) = ⊤ := by
    refine TildeModel619.span_orbit_eq_top Tm vv fun s hs => ?_
    rcases L128P.eq_of_mem_four hZZS hZ2 hZS4 hz₀Z hz₀1 hzlZ hzl hs with e | e | e | e
    · left
      rw [Tm.c_eq_zero_iff, e]
      exact Subgroup.one_mem _
    · left
      rw [Tm.c_eq_zero_iff, e]
      exact hz₀Z
    · right
      rw [hvv]
      exact congrArg Tm.c (Subtype.ext e)
    · right
      have hs' : s = ⟨z₀, hZSU (hZZS hz₀Z)⟩ * ⟨l⁻¹ * z₀ * l, hzlU⟩ := Subtype.ext e
      rw [hs', Tm.c_mul, (Tm.c_eq_zero_iff _).mpr hz₀Z, zero_add]

  obtain ⟨Φ, hΦ⟩ := SzN28.exists_selfDual_equiv B h101.nondegenerate
  let ρK : ↥K →* (Tm.V ≃ₗ[ZMod 2] Tm.V) := Tm.ρ.comp K.subtype
  let σK : ↥K →* (A ≃ₗ[ZMod 2] A) := ρ.comp K.subtype
  have hΦkey : ∀ (ν : Module.Dual (ZMod 2) A) (v : A), (∀ w, B v w = ν w) → Φ ν = v := by
    intro ν v hv
    have h0 := h101.nondegenerate (Φ ν - v) (fun w => by
      rw [map_sub, LinearMap.sub_apply, hΦ, hv w, sub_self])
    exact sub_eq_zero.1 h0
  have hΦeq : ∀ (k : ↥K) (μ : Module.Dual (ZMod 2) A),
      Φ (μ ∘ₗ ((σK k⁻¹ : A ≃ₗ[ZMod 2] A) : A →ₗ[ZMod 2] A)) = σK k (Φ μ) := by
    intro k μ
    apply hΦkey
    intro w'
    have hσk : σK k ∈ ρ.range := ⟨_, rfl⟩
    have h1 := h101.isometry (σK k) hσk (Φ μ) (σK k⁻¹ w')
    have h2 : σK k (σK k⁻¹ w') = w' := by
      have := congrArg (fun f : A ≃ₗ[ZMod 2] A => f w') (mul_inv_cancel (σK k))
      rw [map_inv]
      exact this
    rw [h2] at h1
    rw [h1, hΦ]
    rfl
  have hsplit := SzN28.split_of_dual ρK σK (Tm.phi β hβZ) (Tm.phi_surjective β hβZ hR.1)
    (fun k v => hφρ k v) (fun k z hz => hKZ k z hz) (fun k hk => hker k hk) Φ hΦeq
    (fun u hu => t.fix_eq_zero u fun a' ha' => by
      obtain ⟨k, hk⟩ := hsA a' ha'
      rw [← hk]
      exact hu k)
    (fun δ hδ hδker => t.coh σK (fun k => k.2.2) hsA δ hδ hδker)
  have hker0 := SzN28.ker_eq_bot_of_decomp Tm.ρ (Tm.phi β hβZ) K hKn hsplit.1 hsplit.2 Y hYZ _ hv
    hgen

  obtain ⟨u, huZU, huZ⟩ := IsConcreteLE.exists_of_lt hZlt
  have hu0 : Tm.phi β hβZ (Tm.c ⟨u, huZU.1⟩) = 0 :=
    (Tm.phi_eq_zero_iff β hβZ hR.2.1 _).mpr ⟨⟨u, huZU.1⟩, huZU, rfl⟩
  exact huZ ((Tm.c_eq_zero_iff _).mp (hker0 _ hu0))

end Hyp6Sec2

theorem res6219S8_of_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4)
    (h512 : Stmt5_1_2_F4) (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h626 : Stmt6_2_6_F4)
    (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4) : Res6219S8_F4 := by
  intro G _ _ T M L V h Z H U ZU hlt hZlt l hl hlH X A _ _ _ B β ρ hR h8
  exact h.false_s8_ch619_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hZlt hl hlH hR h8

end CFSG.Quasithin.H13
