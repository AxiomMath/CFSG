module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDelModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceKlein
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDict
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCampbell

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Lift.Piece
open scoped Multiplicative MatrixGroups LinearAlgebra.Projectivization commutatorElement

namespace Piece

theorem forall_eq_of_five {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (h5 : Fintype.card Ω = 5)
    {a b c d e : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    ∀ t : Ω, t = a ∨ t = b ∨ t = c ∨ t = d ∨ t = e := by
  classical
  have hcard : ({a, b, c, d, e} : Finset Ω).card = Fintype.card Ω := by
    rw [h5, Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
      Finset.card_insert_of_notMem (by simp [hcd, hce]),
      Finset.card_insert_of_notMem (by simp [hde]), Finset.card_singleton]
  have hU := Finset.eq_univ_of_card _ hcard
  intro t
  have ht : t ∈ ({a, b, c, d, e} : Finset Ω) := by
    rw [hU]
    exact Finset.mem_univ t
  simpa using ht

theorem exists_mem_modComm_map {G : Type} [Group G] {V : Subgroup G} (A : Subgroup (MulAut V))
    {φ : MulAut V} (hφ : ∀ a ∈ A, φ * a * φ⁻¹ ∈ A) {g : G} (hg : g ∈ modComm V A) :
    ∃ hgV : g ∈ V, ((φ ⟨g, hgV⟩ : V) : G) ∈ modComm V A := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, v, rfl⟩ := hx
    refine ⟨V.mul_mem (a v).2 (V.inv_mem v.2), ?_⟩
    have e : φ ⟨((a v : V) : G) * (v : G)⁻¹, V.mul_mem (a v).2 (V.inv_mem v.2)⟩ =
        ((φ * a * φ⁻¹) (φ v)) * (φ v)⁻¹ := by
      have : (⟨((a v : V) : G) * (v : G)⁻¹, V.mul_mem (a v).2 (V.inv_mem v.2)⟩ : V) = a v * v⁻¹ :=
        rfl
      rw [this, map_mul, map_inv]
      simp
    rw [e]
    exact Subgroup.subset_closure ⟨φ * a * φ⁻¹, hφ a ha, φ v, rfl⟩
  | one =>
    refine ⟨V.one_mem, ?_⟩
    have : (⟨1, V.one_mem⟩ : ↥V) = 1 := rfl
    rw [this, map_one]
    exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    obtain ⟨hxV, hx⟩ := hx
    obtain ⟨hyV, hy⟩ := hy
    refine ⟨V.mul_mem hxV hyV, ?_⟩
    have : (⟨x * y, V.mul_mem hxV hyV⟩ : ↥V) = ⟨x, hxV⟩ * ⟨y, hyV⟩ := rfl
    rw [this, map_mul]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    obtain ⟨hxV, hx⟩ := hx
    refine ⟨V.inv_mem hxV, ?_⟩
    have : (⟨x⁻¹, V.inv_mem hxV⟩ : ↥V) = ⟨x, hxV⟩⁻¹ := rfl
    rw [this, map_inv]
    exact Subgroup.inv_mem _ hx

end Piece

theorem delWProp
    : DelWProp := by
  intro G _ _ R M V n F _ r Lc ctx i Fs P hcore hbase hseed hH0 hmin hbasic himage
  classical
  have hS := ctx.setting
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hS.card_eq]; positivity)
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  let _ : DecidableEq (ℙ F (Fin 2 → F)) := Classical.decEq _
  have hX := ctx.hX
  have hP : P ≤ Subgroup.normalizer (V : Set G) := le_top.trans hX
  have hSP : baum R ≤ P := hbasic.lt.le
  have hSM : baum R ≤ M := (inf_le_left : baum R ≤ R).trans hS.max.1
  have hMP : ¬ P ≤ M := hmin.not_le
  have hVS : V ≤ baum R := hcore.V_le_S
  have hWV : modComm V Fs ≤ V := Piece.modComm_le' V Fs
  have hWS : modComm V Fs ≤ baum R := hWV.trans hVS
  have hWP : modComm V Fs ≤ P := hWS.trans hSP
  obtain ⟨⟨W₀, hW1, hW2, hW3, θ, hmax, himg⟩⟩ := even_SL2_original_images hS ctx.comps
  have hbridge := even_SL2_original_bridge hS ctx.comps
  set ψ := (binPsi θ).toMonoidHom with hψ
  set L : Subgroup G := oddOrderSubgroup (⊤ : Subgroup G) with hL
  have layer := hmax.offenders.family.layer
  have common := hmax.offenders.family.common
  have hdel : DeletedFamily ((autOn (⊤ : Subgroup G) V).map ψ) n r (fun j => (Lc j).map ψ) := by
    have hKL : (autOn L V).map ψ = oddGen ((autOn (⊤ : Subgroup G) V).map ψ) := by
      rw [hbridge.K_eq]
      exact map_closure_odd (binPsi θ) (autOn (⊤ : Subgroup G) V)
    rcases hmax.offenders.family.alternatives with ⟨hnat, -⟩ | ⟨hdel, -⟩
    · exfalso
      apply ctx.deleted
      have hD := (himg.natural hnat).1
      have hle : (autOn (thompsonJ R) V).map ψ ≤ (autOn L V).map ψ := by
        rw [hD, hKL, layer.K_eq]
        exact iSup_mono fun j => inf_le_right
      exact (Subgroup.map_le_map_iff_of_injective (binPsi θ).injective).1 hle
    · exact hdel
  obtain ⟨-, -, ψs, βs, As, h5, hDA, hall⟩ := himg.deleted hdel
  obtain ⟨hcompat, halt, hAle, a, b, c, d, ω, hab, hac, had, hbc, hbd, hcd, hωa, hωb, hωc, hωd,
    hAimg, -, -⟩ := hall i
  have hallpts := Piece.forall_eq_of_five h5 hab hac had hωa.symm hbc hbd hωb.symm hcd hωc.symm
    hωd.symm
  have hFs' : Fs.map ψ ≤ (Lc i).map ψ := Subgroup.map_mono hseed.le
  have hcard' : Nat.card ↥(Fs.map ψ) = 3 := by
    rw [Subgroup.card_map_of_injective (binPsi θ).injective, hseed.card]
  obtain ⟨hcardW, ⟨f₁, hf₁Fs, hf₁ne, hf₁fix⟩, ⟨x₁, hx₁A, w₁, hw₁W, hx₁w₁⟩⟩ :=
    Piece.deleted_cycle_module layer common i h5 (ψs i) (βs i) hcompat hallpts hab hcd hAimg hFs'
      hcard'
  have hAn : autOn P V ≤ Subgroup.normalizer (Fs : Set (MulAut V)) := by
    rw [himage.image]
    exact sup_le Subgroup.le_normalizer hseed.normalized
  have hWn : P ≤ Subgroup.normalizer ((modComm V Fs : Subgroup G) : Set G) := by
    have key : ∀ p ∈ P, ∀ g ∈ modComm V Fs, p * g * p⁻¹ ∈ modComm V Fs := by
      intro p hp g hg
      set φ := rho V P hP ⟨p, hp⟩ with hφ
      have hφn : φ ∈ Subgroup.normalizer (Fs : Set (MulAut V)) :=
        hAn ((mem_autOn_self_iff hP).2 ⟨⟨p, hp⟩, rfl⟩)
      obtain ⟨hgV, hmem⟩ := Piece.exists_mem_modComm_map Fs
        (fun a ha => (Subgroup.mem_normalizer_iff.1 hφn a).1 ha) hg
      have e : ((φ ⟨g, hgV⟩ : V) : G) = p * g * p⁻¹ := rho_apply_coe hP ⟨p, hp⟩ ⟨g, hgV⟩
      rwa [e] at hmem
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key p hp g, fun h => ?_⟩
    have := key p⁻¹ (P.inv_mem hp) _ h
    simpa [mul_assoc] using this
  have helem : IsElemAbelian 2 (modComm V Fs) :=
    Campbell.isElemAbelian_mono hS.reduced.2.2.1 hWV
  have hcardWa : Nat.card ↥(modComm V Fs) = 4 := by
    rw [Nat.card_congr (Piece.modCommEquiv' θ Fs).toEquiv]
    exact (Nat.card_congr (Multiplicative.toAdd : Multiplicative _ ≃ _)).trans hcardW
  have hWfin : Finite ↥(modComm V Fs) := Nat.finite_of_card_ne_zero (by rw [hcardWa]; norm_num)
  have hWnt : Nontrivial ↥(modComm V Fs) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardWa]; norm_num)
  have hklein : IsKleinFour ↥(modComm V Fs) := by
    refine ⟨hcardWa, ?_⟩
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    refine orderOf_eq_prime ?_ hg
    apply Subtype.ext
    simpa using helem.2 (g : G) g.2
  obtain ⟨φ₁, hφ₁Fs, hφ₁ψ⟩ := Subgroup.mem_map.1 hf₁Fs
  have hφ₁ne : φ₁ ≠ 1 := by
    intro h
    apply hf₁ne
    rw [← hφ₁ψ, h, map_one]
  have hφ₁3 : φ₁ ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥Fs) (x := (⟨φ₁, hφ₁Fs⟩ : ↥Fs))
    rw [hseed.card] at h
    exact congrArg Subtype.val h
  have hφ₁fix : ∀ u : ↥V, (u : G) ∈ modComm V Fs → φ₁ u = u → u = 1 := by
    intro u hu hfix
    have hw : vecOf θ u ∈ commGL (Fs.map ψ) ⊤ := (Piece.mem_modComm_iff' θ Fs u).1 hu
    have h1 : f₁ (vecOf θ u) = vecOf θ u := by
      rw [← hφ₁ψ]
      show binPsi θ φ₁ (vecOf θ u) = vecOf θ u
      rw [Piece.binPsi_vecOf', hfix]
    have h0 := hf₁fix _ hw h1
    apply Piece.vecOf_injective' θ
    rw [h0, Piece.vecOf_one']
  have hFsP : Fs ≤ autOn P V := by
    rw [himage.image]
    exact le_sup_left
  have hx₁D : x₁ ∈ (autOn (thompsonJ R) V).map ψ := by
    rw [hDA]
    exact (le_iSup As i) hx₁A
  obtain ⟨y₁, hy₁, hyx₁⟩ := hx₁D
  obtain ⟨g', hg'J, rfl⟩ := mem_autOn_iff.1 hy₁
  have hg'S : (g' : G) ∈ baum R := thompsonJ_le_baum' R hg'J
  have hg'P : (g' : G) ∈ P := hSP hg'S
  have hmove : ∃ u : ↥(modComm V Fs), (g' : G) * (u : G) ≠ (u : G) * g' := by
    by_contra hcon
    push Not at hcon
    apply hx₁w₁
    have hu₀ : ((elOf θ w₁ : ↥V) : G) ∈ modComm V Fs := Piece.elOf_mem_modComm' θ Fs hw₁W
    have hc := hcon ⟨_, hu₀⟩
    have h2 : conjAct V g' (elOf θ w₁) = elOf θ w₁ := by
      apply Subtype.ext
      rw [coe_conjAct_apply]
      have hc' : (g' : G) * ((elOf θ w₁ : ↥V) : G) = ((elOf θ w₁ : ↥V) : G) * g' := hc
      rw [hc', mul_inv_cancel_right]
    have h3 := Piece.binPsi_vecOf' θ (conjAct V g') (elOf θ w₁)
    rw [h2, vecOf_elOf] at h3
    rw [← hyx₁]
    exact h3
  obtain ⟨u₂, hu₂⟩ := hmove
  obtain ⟨p₁, hp₁⟩ := (mem_autOn_self_iff hP).1 (hFsP hφ₁Fs)
  have h3 : Piece.actOn (modComm V Fs) P hWn p₁ ^ 3 = 1 := by
    rw [← map_pow]
    refine (Piece.actOn_eq_one_iff hWn _).2 fun u => ?_
    have hu : (u : G) ∈ V := hWV u.2
    have h1 : rho V P hP (p₁ ^ 3) ⟨u, hu⟩ = ⟨u, hu⟩ := by
      rw [map_pow, hp₁, hφ₁3]
      rfl
    have h2 := congrArg (fun x : ↥V => (x : G)) h1
    simp only [rho_apply_coe] at h2
    calc ((p₁ ^ 3 : ↥P) : G) * u
        = (((p₁ ^ 3 : ↥P) : G) * u * ((p₁ ^ 3 : ↥P) : G)⁻¹) * ((p₁ ^ 3 : ↥P) : G) := by group
      _ = u * ((p₁ ^ 3 : ↥P) : G) := by rw [h2]
  have h31 : Piece.actOn (modComm V Fs) P hWn p₁ ≠ 1 := by
    intro h1
    have hc := (Piece.actOn_eq_one_iff hWn p₁).1 h1
    obtain ⟨u, hu1⟩ := exists_ne (1 : ↥(modComm V Fs))
    apply hu1
    have hu : (u : G) ∈ V := hWV u.2
    have hfix : φ₁ ⟨u, hu⟩ = ⟨u, hu⟩ := by
      rw [← hp₁]
      apply Subtype.ext
      rw [rho_apply_coe, hc u]
      simp
    have h' := hφ₁fix ⟨u, hu⟩ u.2 hfix
    exact Subtype.ext (congrArg (fun x : ↥V => (x : G)) h')
  obtain ⟨k, hk⟩ := hbasic.sylow.2.1 ⟨(g' : G), hg'S⟩
  have h2 : Piece.actOn (modComm V Fs) P hWn ⟨g', hg'P⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨(g' : G), hg'P⟩ : ↥P) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have h21 : Piece.actOn (modComm V Fs) P hWn ⟨g', hg'P⟩ ≠ 1 := by
    intro h1
    exact hu₂ ((Piece.actOn_eq_one_iff hWn _).1 h1 u₂)
  have hind := Piece.exists_induce_of_orders hWn h3 h31 h2 h21
  have hred : IsTwoReducedIn P (modComm V Fs) :=
    Piece.isTwoReduced_of_induce hWP hWn helem hind
  obtain ⟨ρ', ψU, hequiv, hker, hsurj⟩ := Wreath.exists_natural_rep (P := P) (U := modComm V Fs) hWn
  have hρsurj : Function.Surjective ρ' := hsurj.2 hind
  have hφ₁odd : φ₁ ∈ autOn (oddOrderSubgroup P) V := by
    rw [autOn_oddOrderSubgroup hP]
    refine Subgroup.subset_closure ⟨hFsP hφ₁Fs, ?_⟩
    rw [orderOf_eq_prime hφ₁3 hφ₁ne]
    decide
  obtain ⟨b, hbB, hbφ⟩ := mem_autOn_iff.1 hφ₁odd
  have hker' : ψU.toMonoidHom.ker =
      (Subgroup.centralizer (oddOrderSubgroup P : Set G)).subgroupOf (modComm V Fs) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hu
      have h1 : u = 1 := ψU.injective (hu.trans (map_one ψU).symm)
      rw [h1]
      exact Subgroup.one_mem _
    · intro hu
      have hc : (b : G) * (u : G) = (u : G) * b := Subgroup.mem_centralizer_iff.1 hu b hbB
      have hV : (u : G) ∈ V := hWV u.2
      have hfix : φ₁ ⟨u, hV⟩ = ⟨u, hV⟩ := by
        rw [← hbφ]
        apply Subtype.ext
        rw [coe_conjAct_apply, hc, mul_inv_cancel_right]
      have h' := hφ₁fix ⟨u, hV⟩ u.2 hfix
      have h1 : u = 1 := Subtype.ext (congrArg (fun x : ↥V => (x : G)) h')
      rw [h1]
      exact map_one ψU.toMonoidHom
  obtain ⟨ϱ', φ', hset⟩ := Piece.natQuotSetting_of_module (k := ZMod 2) (S := baum R) (P := P)
    (M := M) (W := modComm V Fs) hbasic.sylow hbasic.not_normal hSM hMP hbasic.max hred ρ'
    hρsurj ψU.toMonoidHom ψU.surjective (fun p u u' hu' => hequiv p u u' hu') hker'
  refine ⟨hWS, hcardWa, hred, ⟨ϱ', φ', hset⟩, ?_⟩
  rw [hbase.base.J_S]
  intro hbot
  apply hu₂
  have hmem := Subgroup.commutator_mem_commutator hg'J u₂.2
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

end CFSG.QuasithinUnique.Setup.Lift
