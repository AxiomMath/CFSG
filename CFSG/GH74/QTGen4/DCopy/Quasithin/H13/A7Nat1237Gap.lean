module

public import CFSG.Quasithin.H13.A7Nat1237Gap
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1238Inputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7NatAssembly

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

variable {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem gap1237KeJ_of_F4 (h1222 : Stmt12_2_2_F4) (h331 : Stmt3_3_1_F4) (h1229 : Stmt12_2_9_F4) :
    Gap1237KeJ_F4 := by
  intro G _ _ T L V hyp ψ₀ e hS
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, hTI, -, -⟩ := hall V hyp.irrPlus
  have hLV : L ≤ normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hNM := normalizer_le_of_hyp1223_F4 h331 hyp hVT hTV
  have hpre : A7NatPre T L V ψ₀ :=
    ⟨hVT, hLV, hTV, hS.act, hS.onto, nact_of_lact hLV hS.act hS.onto hNM, hNM, hTI⟩
  obtain ⟨ψ, h, he, -⟩ := hpre.exists_relabel_vecFS hS.weight

  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hTe : T ≤ centralizer ({(e : G)} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hZC hS.mem) t ht))
  have hTK : T ≤ normalizer (Kv hyp e : Set G) := by
    have h1 : T ≤ normalizer ((L ⊓ centralizer ({(e : G)} : Set G) : Subgroup G) : Set G) :=
      fun t ht => A4.mem_normalizer_inf (hyp.normalizes ht) (le_normalizer (hTe ht))
    exact (h1.trans (normalizer_le_normalizer_oTwoUpper _)).trans
      (normalizer_le_normalizer_perfectCore _)
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hJK : ⁅Kv hyp e, thompsonJ T⁆ ≤ Kv hyp e :=
    (le_normalizer_iff_commutator_le_left).1 (hJT.trans hTK)

  suffices hsuff : ∃ A, IsMaxElemAbelian T A ∧ ¬ ⁅Kv hyp e, A⁆ ≤ centralizer (V : Set G) by
    obtain ⟨A₁, hA₁, hKA⟩ := hsuff
    refine le_antisymm ?_ hJK
    calc Kv hyp e = ⁅Kv hyp e, A₁⁆ :=
          Kv_eq_commutator_of_not_le hyp h he (hA₁.1.trans hTK) hKA
      _ ≤ ⁅Kv hyp e, thompsonJ T⁆ :=
          commutator_mono le_rfl (le_iSup₂_of_le A₁ hA₁ le_rfl)

  have hLJ : L = ⁅L, thompsonJ T⁆ := (h1229 G T L V hyp).2 hS.cz
  obtain ⟨A, hAmax, hAV⟩ : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ centralizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    have hJV : thompsonJ T ≤ centralizer (V : Set G) := iSup₂_le fun A hA => hcon A hA
    have hLC : L ≤ centralizer (V : Set G) := by
      rw [hLJ, commutator_le]
      intro l hl j hj
      have hjv := mem_centralizer_iff.1 (hJV hj)
      have hconj : l * j * l⁻¹ ∈ centralizer (V : Set G) := by
        rw [mem_centralizer_iff]
        intro w hw
        have hw' : l⁻¹ * w * l⁻¹⁻¹ ∈ V := (mem_normalizer_iff.1 (hLV (inv_mem hl)) w).1 hw
        rw [inv_inv] at hw'
        have h1 := hjv _ hw'
        calc w * (l * j * l⁻¹) = l * ((l⁻¹ * w * l) * j) * l⁻¹ := by group
          _ = l * (j * (l⁻¹ * w * l)) * l⁻¹ := by rw [h1]
          _ = l * j * l⁻¹ * w := by group
      have := (centralizer (V : Set G)).mul_mem hconj
        ((centralizer (V : Set G)).inv_mem (hJV hj))
      rw [commutatorElement_def]
      exact this
    apply hyp.irrPlus.2.1
    rw [← hyp.irrPlus.2.2.2.1, eq_bot_iff, commutator_le]
    intro v hv l hl
    rw [mem_bot, commutatorElement_def, mem_centralizer_iff.1 (hLC hl) v hv]
    group
  by_cases hcase : ⁅Kv hyp e, A⁆ ≤ centralizer (V : Set G)
  swap
  · exact ⟨A, hAmax, hcase⟩

  set ρ := coordRep ψ (le_refl (normalizer (V : Set G))) h.Nact with hρdef
  have hρL : ∀ l : L, ρ ⟨l, hLV l.2⟩ = (natLam h.L_le h.Lact l : Perm (Fin 7)) := fun l =>
    IsCoordAct.unique ψ (hLV l.2) (coordRep_spec ψ le_rfl h.Nact ⟨l, hLV l.2⟩)
      (natLam_spec h.L_le h.Lact l)
  have hρ1 : ∀ x : normalizer (V : Set G), ρ x = 1 ↔ (x : G) ∈ centralizer (V : Set G) :=
    fun x => coordRep_eq_one_iff ψ le_rfl h.Nact x
  have hρe : ∀ x : normalizer (V : Set G),
      permAct7 (ρ x) vecFS = vecFS → (x : G) ∈ centralizer ({(e : G)} : Set G) := by
    intro x hx
    have hspec := coordRep_spec ψ le_rfl h.Nact x
    let y : V := ⟨(x : G) * e * (x : G)⁻¹, (mem_normalizer_iff.1 x.2 e).1 e.2⟩
    have hy : vec ψ y = vec ψ e := by
      rw [hspec e y rfl, he]
      exact hx
    have hye : (x : G) * e * (x : G)⁻¹ = e := congrArg Subtype.val (vec_injective ψ hy)
    rw [mem_centralizer_singleton_iff]
    calc (x : G) * e = (x : G) * e * (x : G)⁻¹ * x := by group
      _ = e * x := by rw [hye]
  have hρe' : ∀ x : normalizer (V : Set G),
      (x : G) ∈ centralizer ({(e : G)} : Set G) → permAct7 (ρ x) vecFS = vecFS := by
    intro x hx
    have hspec := coordRep_spec ψ le_rfl h.Nact x
    have hxe : (x : G) * e * (x : G)⁻¹ = e := by
      rw [mem_centralizer_singleton_iff.1 hx, mul_inv_cancel_right]
    have h1 := hspec e e hxe.symm
    rw [he] at h1
    exact h1.symm

  have hcomm : ∀ B : Subgroup G, B ≤ T → ⁅Kv hyp e, B⁆ ≤ centralizer (V : Set G) →
      ∀ (b : G) (hbN : b ∈ normalizer (V : Set G)), b ∈ B → ∀ τ ∈ altFive,
        ρ ⟨b, hbN⟩ * (τ : Perm (Fin 7)) = τ * ρ ⟨b, hbN⟩ := by
    intro B hBT hBV b hbN hb τ hτ
    obtain ⟨k, hkK, hk⟩ := exists_mem_Kv_natLam hyp h he hτ
    have hkb : (k : G) * b * (k : G)⁻¹ * b⁻¹ ∈ centralizer (V : Set G) := by
      have := hBV (commutator_mem_commutator hkK hb)
      rwa [commutatorElement_def] at this
    have h1 : ρ (⟨k, hLV k.2⟩ * ⟨b, hbN⟩ * (⟨k, hLV k.2⟩ : normalizer (V : Set G))⁻¹ *
        (⟨b, hbN⟩ : normalizer (V : Set G))⁻¹) = 1 := (hρ1 _).2 hkb
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hρL k, hk] at h1
    have h2 : (τ : Perm (Fin 7)) * ρ ⟨b, hbN⟩ * (τ : Perm (Fin 7))⁻¹ = ρ ⟨b, hbN⟩ := by
      have := mul_eq_one_iff_eq_inv.1 h1
      rwa [inv_inv] at this
    calc ρ ⟨b, hbN⟩ * (τ : Perm (Fin 7))
        = (τ : Perm (Fin 7)) * ρ ⟨b, hbN⟩ * (τ : Perm (Fin 7))⁻¹ * τ := by rw [h2]
      _ = τ * ρ ⟨b, hbN⟩ := by group

  have hA56 : ∀ (a : G) (haN : a ∈ normalizer (V : Set G)), a ∈ A →
      ρ ⟨a, haN⟩ = 1 ∨ ρ ⟨a, haN⟩ = swap 5 6 := by
    intro a haN ha
    have hc := hcomm A hAmax.1 hcase a haN ha
    exact perm_eq_one_or_swap_of_commute (hc _ a5cyc012_mem) (hc _ a5cyc123_mem)
      (hc _ a5cyc234_mem)
  obtain ⟨a₀, ha₀A, ha₀V⟩ : ∃ a ∈ A, a ∉ centralizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hAV hcon
  have ha₀N : a₀ ∈ normalizer (V : Set G) := hTV (hAmax.1 ha₀A)
  have hρa₀ : ρ ⟨a₀, ha₀N⟩ = swap 5 6 := by
    rcases hA56 a₀ ha₀N ha₀A with h1 | h1
    · exact absurd ((hρ1 _).1 h1) ha₀V
    · exact h1

  obtain ⟨x, hxL, hx⟩ := h.Lonto (dbl0516 : Perm (Fin 7)) dbl0516.2
  have hxN : x ∈ normalizer (V : Set G) := hLV hxL
  have hρx : ρ ⟨x, hxN⟩ = dbl0516 :=
    IsCoordAct.unique ψ hxN (coordRep_spec ψ le_rfl h.Nact ⟨x, hxN⟩) hx

  have hYC : A.map (MulAut.conj x).toMonoidHom ≤
      centralizer ({(e : G)} : Set G) ⊓ normalizer (V : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    change x * a * x⁻¹ ∈ centralizer ({(e : G)} : Set G) ⊓ normalizer (V : Set G)
    have haN : a ∈ normalizer (V : Set G) := hTV (hAmax.1 ha)
    have hyN : x * a * x⁻¹ ∈ normalizer (V : Set G) :=
      (normalizer (V : Set G)).mul_mem ((normalizer (V : Set G)).mul_mem hxN haN)
        ((normalizer (V : Set G)).inv_mem hxN)
    refine ⟨?_, hyN⟩
    have hρy : ρ ⟨x * a * x⁻¹, hyN⟩ =
        (dbl0516 : Perm (Fin 7)) * ρ ⟨a, haN⟩ * (dbl0516 : Perm (Fin 7))⁻¹ := by
      have : (⟨x * a * x⁻¹, hyN⟩ : normalizer (V : Set G)) =
          ⟨x, hxN⟩ * ⟨a, haN⟩ * (⟨x, hxN⟩ : normalizer (V : Set G))⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hρx]
    apply hρe ⟨x * a * x⁻¹, hyN⟩
    rw [hρy]
    rcases hA56 a haN ha with h1 | h1
    · rw [h1, mul_one, mul_inv_cancel]
      decide
    · rw [h1, dbl0516_conj_swap]
      decide
  have hTC : T ≤ centralizer ({(e : G)} : Set G) ⊓ normalizer (V : Set G) := le_inf hTe hTV
  have hTsyl : QuasithinUnique.IsSylowTwoOf T
      (centralizer ({(e : G)} : Set G) ⊓ normalizer (V : Set G)) :=
    isSylowTwoOf_of_le hyp.sylow hTC
  have hYel := isElemAbelian_map_conj hAmax.2.1 x
  have hY2 : IsPGroup 2 (A.map (MulAut.conj x).toMonoidHom) := fun y =>
    ⟨1, Subtype.ext (by
      simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
      exact hYel.2 y y.2)⟩
  obtain ⟨S', hYS', hS'⟩ := QuasithinUnique.exists_isSylowTwoOf_of_le hYC hY2
  obtain ⟨c, hcC, hS'eq⟩ := hTsyl.exists_conj hS'
  have hcN : c ∈ normalizer (V : Set G) := hcC.2

  have hA₁T : A.map (MulAut.conj (c⁻¹ * x)).toMonoidHom ≤ T := by
    rintro _ ⟨a, ha, rfl⟩
    have hy : x * a * x⁻¹ ∈ S' := hYS' ⟨a, ha, rfl⟩
    rw [hS'eq] at hy
    obtain ⟨t, ht, hty⟩ := hy
    have hty' : c * t * c⁻¹ = x * a * x⁻¹ := hty
    change (c⁻¹ * x) * a * (c⁻¹ * x)⁻¹ ∈ T
    have : (c⁻¹ * x) * a * (c⁻¹ * x)⁻¹ = t := by
      calc (c⁻¹ * x) * a * (c⁻¹ * x)⁻¹ = c⁻¹ * (x * a * x⁻¹) * c := by group
        _ = c⁻¹ * (c * t * c⁻¹) * c := by rw [hty']
        _ = t := by group
    rw [this]
    exact ht
  have hA₁max : IsMaxElemAbelian T (A.map (MulAut.conj (c⁻¹ * x)).toMonoidHom) := by
    refine ⟨hA₁T, isElemAbelian_map_conj hAmax.2.1 _, fun B hBT hB => ?_⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj (c⁻¹ * x)).injective]
    exact hAmax.2.2 B hBT hB
  refine ⟨_, hA₁max, fun hcon => ?_⟩

  have ha₁A : (c⁻¹ * x) * a₀ * (c⁻¹ * x)⁻¹ ∈ A.map (MulAut.conj (c⁻¹ * x)).toMonoidHom :=
    ⟨a₀, ha₀A, rfl⟩
  have ha₁N : (c⁻¹ * x) * a₀ * (c⁻¹ * x)⁻¹ ∈ normalizer (V : Set G) := hTV (hA₁T ha₁A)
  have hρa₁ : ρ ⟨(c⁻¹ * x) * a₀ * (c⁻¹ * x)⁻¹, ha₁N⟩ =
      (ρ ⟨c, hcN⟩)⁻¹ * swap 0 1 * ρ ⟨c, hcN⟩ := by
    have : (⟨(c⁻¹ * x) * a₀ * (c⁻¹ * x)⁻¹, ha₁N⟩ : normalizer (V : Set G)) =
        ((⟨c, hcN⟩ : normalizer (V : Set G))⁻¹ * ⟨x, hxN⟩) * ⟨a₀, ha₀N⟩ *
          ((⟨c, hcN⟩ : normalizer (V : Set G))⁻¹ * ⟨x, hxN⟩)⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, map_mul, map_inv, hρx, hρa₀, ← dbl0516_conj_swap]
    group
  have hce : permAct7 (ρ ⟨c, hcN⟩) vecFS = vecFS := hρe' ⟨c, hcN⟩ hcC.1
  have h56 := (permAct7_vecFS_iff _).1 hce
  have hpq : (ρ ⟨c, hcN⟩)⁻¹ 0 ≠ (ρ ⟨c, hcN⟩)⁻¹ 1 := fun h' =>
    absurd ((ρ ⟨c, hcN⟩)⁻¹.injective h') (by decide)
  have hout : ∀ i : Fin 7, (i : ℕ) < 5 → ((ρ ⟨c, hcN⟩)⁻¹ i : ℕ) < 5 := by
    intro i hi
    have hlt := ((ρ ⟨c, hcN⟩)⁻¹ i).isLt
    by_contra hge
    push Not at hge
    have hv : ∀ j : Fin 7, 5 ≤ (j : ℕ) → j = 5 ∨ j = 6 := by decide
    have hπi : ρ ⟨c, hcN⟩ ((ρ ⟨c, hcN⟩)⁻¹ i) = i := Equiv.Perm.eq_inv_iff_eq.1 rfl
    rcases hv _ hge with h5 | h6
    · rw [h5] at hπi
      rcases h56 with ⟨h5', -⟩ | ⟨h5', -⟩ <;> rw [h5'] at hπi <;> rw [← hπi] at hi <;>
        exact absurd hi (by decide)
    · rw [h6] at hπi
      rcases h56 with ⟨-, h6'⟩ | ⟨-, h6'⟩ <;> rw [h6'] at hπi <;> rw [← hπi] at hi <;>
        exact absurd hi (by decide)
  have hswap : ρ ⟨(c⁻¹ * x) * a₀ * (c⁻¹ * x)⁻¹, ha₁N⟩ =
      swap ((ρ ⟨c, hcN⟩)⁻¹ 0) ((ρ ⟨c, hcN⟩)⁻¹ 1) := by
    rw [hρa₁, swap_apply_apply, inv_inv]

  have hc := hcomm _ hA₁T hcon _ ha₁N ha₁A
  apply not_commute_swap_of_lt_five _ _ hpq (hout 0 (by decide)) (hout 1 (by decide))
  rw [← hswap]
  exact ⟨hc _ a5cyc012_mem, hc _ a5cyc123_mem, hc _ a5cyc234_mem⟩

end CFSG.Quasithin.H13.A7
