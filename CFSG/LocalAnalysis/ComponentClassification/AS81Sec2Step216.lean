module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step216Ker
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step215
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2LocalQ
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2OmegaPts
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Psi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

namespace Sec2Five

open Equiv

@[expose] def σ5 : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

theorem σ5_mem : σ5 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem exists_eq_act_add : ∀ v : Fin 5 → ZMod 2, Sec2V4.IsEven v →
    ∃ u : Fin 5 → ZMod 2, Sec2V4.IsEven u ∧ v = Sec2V4.act σ5 u + u := by
  decide +kernel

theorem eq_zero_of_act_add : ∀ u : Fin 5 → ZMod 2, Sec2V4.IsEven u →
    Sec2V4.act σ5 u + u = 0 → u = 0 := by
  decide +kernel

theorem not_isMulCommutative : ¬ IsMulCommutative (alternatingGroup (Fin 5)) := by
  intro h
  let a : alternatingGroup (Fin 5) :=
    ⟨swap 0 1 * swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  let b : alternatingGroup (Fin 5) :=
    ⟨swap 0 1 * swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  exact absurd (h.is_comm.comm a b) (by decide)

end Sec2Five

namespace Sec2Nat

open Equiv

@[expose] def tau0 : Perm (Fin 6) := swap 0 1 * swap 4 5

theorem tau0_mem : tau0 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem act_tau0_z0 : act tau0 z0 = z0 := by
  decide

@[expose] def w2 : Fin 6 → ZMod 2 := ![1, 0, 1, 0, 0, 0]

theorem sum_w2 : ∑ i, w2 i = 0 := by
  rw [Fin.sum_univ_six]
  decide

theorem w2_mem_lay_two : w2 ∈ lay d0 2 := by
  rw [mem_lay_d0_two sum_w2]
  decide

theorem act_tau0_w2_not_mem : act tau0 w2 ∉ lay d0 2 := by
  rw [mem_lay_d0_two ((sum_act tau0 w2).trans sum_w2)]
  decide

end Sec2Nat

namespace Sec2

variable {G : Type} [Group G]

theorem conj_mem_timmesfeldOmega
    {g x : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm)
    (hx : x ∈ timmesfeldOmega qMinus) : g * x * g⁻¹ ∈ timmesfeldOmega qMinus := by
  rw [Sec2Omega.timmesfeldOmega_qMinus] at hx ⊢
  have h1 := Subgroup.map_commutator (TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm)
    (TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm) (MulAut.conj g).toMonoidHom
  have h2 : (TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm).map
      (MulAut.conj g).toMonoidHom = TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg)
  rw [h2] at h1
  rw [← h1]
  exact ⟨x, hx, rfl⟩

theorem mul_inv_mem_zpowers [Finite G] {Z : Subgroup G} {z : G} (hz : orderOf z = 2)
    (hzZ : z ∈ Z) (hZ4 : Nat.card Z = 4) {a b : G} (ha : a ∈ Z) (hb : b ∈ Z)
    (haz : a ∉ zpowers z) (hbz : b ∉ zpowers z) : a * b⁻¹ ∈ zpowers z := by
  have hidx : ((zpowers z).subgroupOf Z).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card (zpowers z) Z
    rw [inf_eq_left.mpr (zpowers_le.mpr hzZ), Nat.card_zpowers, hz, hZ4] at h1
    rw [← Subgroup.relIndex]
    omega
  have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩⁻¹)).mpr
    ⟨fun h' => absurd h' haz, fun h' => (hbz (by
      have h'' := inv_mem h'
      rw [inv_inv] at h''
      exact h'')).elim⟩
  exact h

end Sec2

namespace Sec2Q

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F T₀ Q : Subgroup G}
  {u y z : G}

open Sec2

theorem exists_t_of (h21 : Step21) (h24 : Step24) (h26 : Step26) (h212 : Step212)
    (hQ : Sec2Q G A R g E F T₀ Q u y z) :
    ∃ t ∈ Q, (∀ τ ∈ sec2T E T₀, τ ∈ sec2H E F ∨ t * τ ∈ sec2H E F) ∧
      ∃ W : Subgroup G, Nat.card W = 64 ∧ W ≤ Q ∧ W ≤ sec2S A R E F ∧
        ∀ s ∈ sec2S A R E F, s * t * s⁻¹ * t⁻¹ ∈ sec2Z A E F → s ∈ W := by
  have hd := hQ.data
  have hset := hd.setting
  have hS : Special (sec2S A R E F) (sec2Z A E F) := special_of h24 hset
  obtain ⟨C⟩ := nonempty_coord h26 hset
  obtain ⟨-, hSH, -, -, -, -, -, hHS, -⟩ := h26 G A R g E F hset
  obtain ⟨-, hPE, -, -, -, -, -, -, hSPE, -⟩ := h21 G A R g E F hset
  obtain ⟨-, hPST, ⟨x, hx3, hxF4, hxcl, hxH, hxH', θ, hθ, hker⟩, -, -, -⟩ :=
    (h212 G A R g E F hset).2 T₀ hd.le hd.sylow
  have hx : XData (sec2S A R E F) (sec2Z A E F) x :=
    ⟨hxF4.1, hxF4.2.1, by rw [← hx3, pow_orderOf_eq_one], hxcl, hxF4.2.2⟩
  have hT₀2 : IsPGroup 2 T₀ := hd.sylow.isPGroup
  have hT2 : IsPGroup 2 (sec2T E T₀) := hT₀2.to_le inf_le_left
  have hST : sec2S A R E F ≤ sec2T E T₀ := le_sup_right.trans hPST
  have hS2 : IsPGroup 2 (sec2S A R E F) := hT2.to_le hST
  have hKN : sec2H E F ⊔ sec2T E T₀ ⊔ zpowers x ≤ normalizer (sec2S A R E F : Set G) :=
    sup_le (sup_le hHS (inf_le_left.trans hd.sylow.le)) (zpowers_le.mpr hxF4.1)
  obtain ⟨hinf, hsup⟩ := semidirect C hS hx hker hS2 hx3 hxH'
    (hSH.trans (le_sup_left.trans le_sup_left))
  have hPH : sec2P E ≤ sec2H E F := le_sup_left
  have hP4 : (sec2S A R E F).relIndex (sec2P E) = 4 := by
    have h1 := Subgroup.relIndex_mul_relIndex E (sec2S A R E F ⊓ sec2P E) (sec2P E) hSPE.1
      inf_le_right
    rw [hSPE.2.1, hPE.2.1, Subgroup.inf_relIndex_right] at h1
    omega
  have hP4' : (sec2P E ⊓ sec2S A R E F).relIndex (sec2P E) = 4 := by
    rw [Subgroup.inf_relIndex_left]
    exact hP4
  obtain ⟨t₀, ht₀, h0, h1, h2⟩ := exists_t₀ C hθ hker hS2 hT2 hx3 hxH'
    (le_sup_left.trans hPST) hPH hP4'
  obtain ⟨t, htT, htt, htx, htS, htN, hcompl, hTH, -, -⟩ := exists_t C hker hSH hST hS2 hT2 hx3
    (θ_x C hker hS2 hx3 hxH') hKN hinf hsup ht₀ h0 h1 h2
  have ht : TData (sec2S A R E F) (sec2H E F) x t := ⟨htN, htt, htx, htS, hcompl⟩
  obtain ⟨z', hzZ, hz1, hz⟩ := exists_z hS hx ht
  have hD : QSetting (sec2S A R E F) (sec2Z A E F) (sec2H E F) x t z' :=
    ⟨hS, hSH, hHS, hx, hxH, hxH', ht, hzZ, hz1, hz⟩
  have hyH : y ∈ sec2H E F := hd.uy.2.2.2.1.1.1
  have hQHT : sec2H E F ⊔ sec2T E T₀ ≤ normalizer (hD.Q : Set G) :=
    C.le_normalizer_Qt hS hHS ht hTH
  have hQeq : hD.Q = Q := hQ.unique _ (C.isQ8Cube_Qt hS hHS hx ht hzZ hz1 hz) (hD.Q_le hST htT)
    (hQHT (mem_sup_left hyH))
  refine ⟨t, hQeq ▸ hS.t_mem_Qt ht.normS ht.sq, hTH, hS.Wt t, C.card_Wt hS hx ht,
    hQeq ▸ hS.Wt_le_Qt ht.normS ht.sq, hS.Wt_le, fun s hs hst => ⟨hs, hst⟩⟩

section Rho

variable (hQ : Sec2Q G A R g E F T₀ Q u y z) {ψ : G → (Fin 6 → ZMod 2)}
  (hadd : ∀ a ∈ Q, ∀ b ∈ Q, ψ (a * b) = ψ a + ψ b)
  (hsurj : ∀ v : Fin 6 → ZMod 2, ∃ a ∈ Q, ψ a = v)
  (hker : ∀ a ∈ Q, ψ a = 0 ↔ a ∈ zpowers z)
  (hsq : ∀ a ∈ Q, qMinus (ψ a) = 0 ↔ a * a = 1) {K : Subgroup G}
  (hK : K ≤ normalizer (Q : Set G) ⊓ centralizer ({z} : Set G))

include hQ in
theorem rho_eq_one_of_mem {q : G} (hq : q ∈ Q) (hqK : q ∈ K) :
    rho hadd hsurj hker hK ⟨q, hqK⟩ = 1 :=
  (rho_eq_one_iff hadd hsurj hker hK _).mpr fun _ ha =>
    commutator_mem_zpowers hQ.q8 hQ.centerIn_Q hq ha

include hQ hsq in
theorem rho_mem_omega_of_mem_sec2H (h24 : Step24) (h26 : Step26) (hZQ : sec2Z A E F ≤ Q)
    (hHK : sec2H E F ≤ K) {h : G} (hh : h ∈ sec2H E F) :
    rho hadd hsurj hker hK ⟨h, hHK hh⟩ ∈ timmesfeldOmega qMinus := by
  classical
  have hS := hQ.data.setting
  have hSp : Special (sec2S A R E F) (sec2Z A E F) := special_of h24 hS
  obtain ⟨C⟩ := nonempty_coord h26 hS
  obtain ⟨-, hSH, -, -, -, -, -, -, -⟩ := h26 G A R g E F hS
  set ρ := rho hadd hsurj hker hK with hρ
  have hO : ∀ k : ↥K, ρ k ∈ TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm :=
    rho_mem_orthogonalGroup hadd hsurj hker hK hsq
  obtain ⟨h₅, hh₅⟩ := C.surj ⟨Sec2Five.σ5, Sec2Five.σ5_mem⟩
  obtain ⟨-, -, -, -, -, -, -, hHS, -⟩ := h26 G A R g E F hS
  have hSΩ : ∀ s (hs : s ∈ sec2S A R E F), ρ ⟨s, hHK (hSH hs)⟩ ∈ timmesfeldOmega qMinus := by
    intro s hs
    obtain ⟨hv₁, hv₂⟩ := C.Ψ_even hSp hs
    obtain ⟨u₁, hu₁, he₁⟩ := Sec2Five.exists_eq_act_add _ hv₁
    obtain ⟨u₂, hu₂, he₂⟩ := Sec2Five.exists_eq_act_add _ hv₂
    obtain ⟨b, hb, hbu⟩ := C.exists_Ψ_eq hu₁ hu₂
    have hcb : (h₅ : G) * b * (h₅ : G)⁻¹ ∈ sec2S A R E F :=
      (mem_normalizer_iff.mp (hHS h₅.2) b).mp hb
    have hcS : (h₅ : G) * b * (h₅ : G)⁻¹ * b⁻¹ ∈ sec2S A R E F := mul_mem hcb (inv_mem hb)
    have hΨc : C.Ψ ((h₅ : G) * b * (h₅ : G)⁻¹ * b⁻¹) = C.Ψ s := by
      rw [C.Ψ_mul hSp hcb (inv_mem hb), C.Ψ_inv hSp hb, C.Ψ_conj hSp h₅ hb, hbu, hh₅]
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_add]
        exact he₁.symm
      · rw [Prod.snd_add]
        exact he₂.symm
    have hsc : s * ((h₅ : G) * b * (h₅ : G)⁻¹ * b⁻¹)⁻¹ ∈ sec2Z A E F :=
      (C.Ψ_eq_iff hSp hs hcS).mp hΨc.symm
    have e : (⟨s, hHK (hSH hs)⟩ : ↥K) =
        ⟨s * ((h₅ : G) * b * (h₅ : G)⁻¹ * b⁻¹)⁻¹,
          hHK (hSH (mul_mem hs (inv_mem hcS)))⟩ *
        (⟨(h₅ : G), hHK h₅.2⟩ * ⟨b, hHK (hSH hb)⟩ * ⟨(h₅ : G), hHK h₅.2⟩⁻¹ *
          ⟨b, hHK (hSH hb)⟩⁻¹) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e, map_mul, rho_eq_one_of_mem hQ hadd hsurj hker hK (hZQ hsc), one_mul,
      Sec2Omega.timmesfeldOmega_qMinus]
    have := Subgroup.commutator_mem_commutator (hO ⟨(h₅ : G), hHK h₅.2⟩) (hO ⟨b, hHK (hSH hb)⟩)
    simpa only [commutatorElement_def, map_mul, map_inv] using this
  have hperf : commutator (alternatingGroup (Fin 5)) = ⊤ :=
    CFSG.GroupTheory.commutator_eq_top_of_isSimpleGroup (alternatingGroup.isSimpleGroup (by simp))
      Sec2Five.not_isMulCommutative
  set f : ↥(sec2H E F) →* ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) :=
    ρ.comp (inclusion hHK) with hf
  have hY : commutator ↥(sec2H E F) ⊔ (sec2S A R E F).subgroupOf (sec2H E F) ≤
      (timmesfeldOmega qMinus).comap f := by
    refine sup_le ?_ fun k hk => hSΩ (k : G) hk
    rw [← map_le_iff_le_comap, _root_.commutator_def, Subgroup.map_commutator,
      Sec2Omega.timmesfeldOmega_qMinus]
    refine Subgroup.commutator_mono ?_ ?_ <;>
      rintro _ ⟨k, -, rfl⟩ <;> exact hO _
  have htop : commutator ↥(sec2H E F) ⊔ (sec2S A R E F).subgroupOf (sec2H E F) = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have hk : C.φ k ∈ (commutator ↥(sec2H E F)).map C.φ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, map_top_of_surjective C.φ C.surj,
        ← _root_.commutator_def, hperf]
      exact mem_top _
    obtain ⟨k', hk', hkk'⟩ := hk
    have h1 : k'⁻¹ * k ∈ (sec2S A R E F).subgroupOf (sec2H E F) := by
      rw [← C.ker, MonoidHom.mem_ker, map_mul, map_inv, hkk', inv_mul_cancel]
    have e : k = k' * (k'⁻¹ * k) := by group
    rw [e]
    exact mul_mem (mem_sup_left hk') (mem_sup_right h1)
  exact hY (htop ▸ mem_top (⟨h, hh⟩ : ↥(sec2H E F)))

include hQ in
theorem le_card_map_sec2H (h24 : Step24) (h26 : Step26) (h212 : Step212)
    (hHK : sec2H E F ≤ K) {t : G} (htQ : t ∈ Q) {W : Subgroup G} (hW64 : Nat.card W = 64)
    (hWQ : W ≤ Q) (hWS : W ≤ sec2S A R E F)
    (hWt : ∀ s ∈ sec2S A R E F, s * t * s⁻¹ * t⁻¹ ∈ sec2Z A E F → s ∈ W) :
    960 ≤ Nat.card (((sec2H E F).subgroupOf K).map (rho hadd hsurj hker hK)) := by
  classical
  have hS := hQ.data.setting
  have hSp : Special (sec2S A R E F) (sec2Z A E F) := special_of h24 hS
  obtain ⟨C⟩ := nonempty_coord h26 hS
  obtain ⟨-, hSH, -, -, -, -, -, hHS, -⟩ := h26 G A R g E F hS
  set ρ := rho hadd hsurj hker hK with hρ
  have hzZ : zpowers z ≤ sec2Z A E F := zpowers_le.mpr (hQ.z_mem_Z h212)
  set f : ↥(sec2H E F) →* ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) :=
    ρ.comp (inclusion hHK) with hf
  have hstep : ∀ k (hk : k ∈ sec2H E F), ρ ⟨k, hHK hk⟩ = 1 → k ∈ sec2S A R E F := by
    have hn : (f.ker.map C.φ).Normal := (MonoidHom.normal_ker f).map C.φ C.surj
    rcases hn.eq_bot_or_eq_top with hb | ht
    · intro k hk hk1
      have h1 : C.φ ⟨k, hk⟩ ∈ f.ker.map C.φ := ⟨⟨k, hk⟩, hk1, rfl⟩
      rw [hb, mem_bot] at h1
      have h2 : (⟨k, hk⟩ : ↥(sec2H E F)) ∈ C.φ.ker := h1
      rw [C.ker] at h2
      exact h2
    · exfalso
      obtain ⟨x, hx, hxσ⟩ : (⟨Sec2Five.σ5, Sec2Five.σ5_mem⟩ : alternatingGroup (Fin 5)) ∈
          f.ker.map C.φ := by
        rw [ht]
        exact mem_top _
      have hx1 : ρ ⟨x, hHK x.2⟩ = 1 := hx
      rw [rho_eq_one_iff] at hx1
      have hWZ : W ≤ sec2Z A E F := by
        intro s hs
        have hsS := hWS hs
        have hxs : (x : G) * s * (x : G)⁻¹ ∈ sec2S A R E F :=
          (mem_normalizer_iff.mp (hHS x.2) s).mp hsS
        have h1 : (x : G) * s * (x : G)⁻¹ * s⁻¹ ∈ sec2Z A E F := hzZ (hx1 s (hWQ hs))
        have h2 := (C.Ψ_eq_zero_iff hSp (mul_mem hxs (inv_mem hsS))).mpr h1
        rw [C.Ψ_mul hSp hxs (inv_mem hsS), C.Ψ_inv hSp hsS, C.Ψ_conj hSp x hsS, hxσ] at h2
        obtain ⟨he₁, he₂⟩ := C.Ψ_even hSp hsS
        have h5 := Sec2Five.eq_zero_of_act_add _ he₁ (congrArg Prod.fst h2)
        have h6 := Sec2Five.eq_zero_of_act_add _ he₂ (congrArg Prod.snd h2)
        exact (C.Ψ_eq_zero_iff hSp hsS).mp (Prod.ext h5 h6)
      have := Subgroup.card_le_of_le hWZ
      rw [hW64, hSp.card] at this
      omega
  have hle : (((sec2H E F).subgroupOf K ⊓ ρ.ker).map K.subtype) ≤ W := by
    rintro _ ⟨k, ⟨hkH, hk1⟩, rfl⟩
    have hkS : (k : G) ∈ sec2S A R E F := hstep k hkH hk1
    exact hWt k hkS (hzZ ((rho_eq_one_iff hadd hsurj hker hK k).mp hk1 t htQ))
  have h1 := Sec2.card_eq_card_inf_ker_mul_card_map' ρ ((sec2H E F).subgroupOf K)
  have h2 : Nat.card ((sec2H E F).subgroupOf K ⊓ ρ.ker : Subgroup ↥K) ≤ 64 := by
    rw [← hW64, ← card_map_of_injective K.subtype_injective]
    exact Subgroup.card_le_of_le hle
  have hH : Nat.card ((sec2H E F).subgroupOf K) = 61440 := by
    rw [NXKernel.card_subgroupOf, inf_eq_left.mpr hHK]
    have hidx : (sec2S A R E F).relIndex (sec2H E F) = 60 := by
      rw [Subgroup.relIndex, ← C.ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr C.surj,
        Subgroup.card_top, Sec2V4.card_alternatingGroup_five]
    have h3 := Subgroup.relIndex_mul_card (sec2S A R E F) (sec2H E F)
    rw [hidx, inf_eq_left.mpr hSH, C.card_S hSp] at h3
    omega
  rw [hH] at h1
  by_contra hlt
  push Not at hlt
  have h4 : Nat.card ((sec2H E F).subgroupOf K ⊓ ρ.ker : Subgroup ↥K) *
      Nat.card (((sec2H E F).subgroupOf K).map ρ) ≤ 64 * 959 :=
    Nat.mul_le_mul h2 (by omega)
  omega

end Rho

theorem exists_mem_conj_not_mem_sec2Z (h211N : Step211Natural) (h212 : Step212)
    (h215 : Step215) (hQ : Sec2Q G A R g E F T₀ Q u y z) :
    ∃ c ∈ sec2K E ⊓ centralizer ({z} : Set G), ∃ w ∈ sec2Z A E F,
      c * w * c⁻¹ ∉ sec2Z A E F := by
  classical
  have hS := hQ.data.setting
  have hF := hS.frame
  obtain ⟨φ, θ, hφs, -, hθadd, hθV, hθsurj, hθker, hθconj⟩ := h211N G A R g E F hS
  obtain ⟨hTsyl, -, -⟩ := h215 G A R g E F T₀ Q u y z hQ
  obtain ⟨-, hPST, -, hZ2, -, -⟩ := (h212 G A R g E F hS).2 T₀ hQ.data.le hQ.data.sylow
  have hTK : sec2T E T₀ ≤ sec2K E := inf_le_right
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 6) (by rw [hF.cardE]; norm_num)
  have hEP : E ≤ sec2P E := le_sec2P hE2 le_normalizer le_rfl
  have hVT : E ⊓ A ≤ sec2T E T₀ := inf_le_left.trans (hEP.trans (le_sup_left.trans hPST))
  have hθT : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → θ v ∈ sec2T E T₀ :=
    fun v hv => hVT (hθV v hv)
  obtain ⟨γ, -, -, hlay⟩ := exists_conj_layers hTK hTsyl hφs hθadd hθker hθconj hθT
  set g' : Equiv.Perm (Fin 6) := (γ : Equiv.Perm (Fin 6)) with hg'
  have hZV : sec2Z A E F ≤ E ⊓ A := by
    rw [hF.sec2Z_eq]
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  obtain ⟨zb, hzb, hzbz⟩ := hθsurj z (hZV (hQ.z_mem_Z h212))
  have hzbar : Sec2Nat.act g'⁻¹ zb = Sec2Nat.z0 ∨ Sec2Nat.act g'⁻¹ zb = Sec2Nat.z0 + 1 := by
    have h1 : z ∈ (Subgroup.upperCentralSeries ↥(sec2T E T₀) 1).map (sec2T E T₀).subtype := by
      rw [Subgroup.upperCentralSeries_one, ← Sec2.centerIn_eq_map, hQ.center]
      exact mem_zpowers z
    rw [← hzbz, hlay 1 hzb, Sec2Nat.mem_lay_d0_one ((Sec2Nat.sum_act _ _).trans hzb)] at h1
    have hz1 : z ≠ 1 := by
      intro h
      have := hQ.order
      rw [h, orderOf_one] at this
      norm_num at this
    rcases h1 with h | h | h | h
    · exfalso
      apply hz1
      rw [← hzbz]
      exact (hθker zb hzb).mpr
        (Or.inl (Sec2Nat.act_injective g'⁻¹ (h.trans (Sec2Nat.act_zero _).symm)))
    · exfalso
      apply hz1
      rw [← hzbz]
      exact (hθker zb hzb).mpr
        (Or.inr (Sec2Nat.act_injective g'⁻¹ (h.trans (Sec2Nat.act_ones _).symm)))
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨c, hc⟩ := hφs (γ * ⟨Sec2Nat.tau0, Sec2Nat.tau0_mem⟩ * γ⁻¹)
  have hcperm : ((φ c : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
      g' * Sec2Nat.tau0 * g'⁻¹ := by
    rw [hc]
    simp [hg']
  have hact : ∀ v, Sec2Nat.act ((φ c : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) v =
      Sec2Nat.act g' (Sec2Nat.act Sec2Nat.tau0 (Sec2Nat.act g'⁻¹ v)) := fun v => by
    rw [hcperm, Sec2Nat.act_mul, Sec2Nat.act_mul]
  have hcz : (c : G) ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h2 : Sec2Nat.act ((φ c : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) zb = zb := by
      rw [hact]
      have h3 : Sec2Nat.act Sec2Nat.tau0 (Sec2Nat.act g'⁻¹ zb) = Sec2Nat.act g'⁻¹ zb := by
        rcases hzbar with h | h
        · rw [h, Sec2Nat.act_tau0_z0]
        · rw [h, Sec2Nat.act_add, Sec2Nat.act_tau0_z0, Sec2Nat.act_ones]
      rw [h3, ← Sec2Nat.act_mul, mul_inv_cancel, Sec2Nat.act_one]
    have h4 := hθconj c zb hzb
    change (c : G) * θ zb * (c : G)⁻¹ =
      θ (Sec2Nat.act ((φ c : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) zb) at h4
    rw [h2, hzbz] at h4
    calc (c : G) * z = (c : G) * z * (c : G)⁻¹ * c := by group
      _ = z * c := by rw [h4]
  have hw2 : ∑ i, Sec2Nat.act g' Sec2Nat.w2 i = 0 :=
    (Sec2Nat.sum_act _ _).trans Sec2Nat.sum_w2
  have hwZ : θ (Sec2Nat.act g' Sec2Nat.w2) ∈ sec2Z A E F := by
    rw [← hZ2, hlay 2 hw2, Sec2Nat.act_inv_act]
    exact Sec2Nat.w2_mem_lay_two
  refine ⟨c, ⟨c.2, hcz⟩, _, hwZ, ?_⟩
  have h5 := hθconj c _ hw2
  change (c : G) * θ (Sec2Nat.act g' Sec2Nat.w2) * (c : G)⁻¹ =
    θ (Sec2Nat.act ((φ c : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))
      (Sec2Nat.act g' Sec2Nat.w2)) at h5
  rw [h5, hcperm, ← hZ2, hlay 2 ((Sec2Nat.sum_act _ _).trans hw2), Sec2Nat.act_conj]
  exact Sec2Nat.act_tau0_w2_not_mem

end Sec2Q

open Sec2 in
theorem step216_of (h21 : Step21) (h24 : Step24) (h26 : Step26)
    (h211N : Step211Natural) (h212 : Step212) (h215 : Step215) : Step216 := by
  intro G _ _ A R g E F T₀ Q u y z hQ
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hQ.data.setting
  have hSp : Special (sec2S A R E F) (sec2Z A E F) := special_of h24 hS
  obtain ⟨C⟩ := nonempty_coord h26 hS
  obtain ⟨-, hSH, -, -, -, -, -, hHS, -⟩ := h26 G A R g E F hS
  obtain ⟨-, hZS, -, -⟩ := h24 G A R g E F hS
  obtain ⟨-, ⟨-, hPE, -⟩, -, -, -, -, -, -, ⟨-, hSPE, -⟩, -⟩ := h21 G A R g E F hS
  obtain ⟨-, hPST, -, hZ2, -, -⟩ := (h212 G A R g E F hS).2 T₀ hQ.data.le hQ.data.sylow
  obtain ⟨-, h215ii, h215iii⟩ := h215 G A R g E F T₀ Q u y z hQ
  obtain ⟨ψ, hadd, hsurj, hker, hsq⟩ := exists_psi hQ.q8 hQ.centerIn_Q
  have hZV : sec2Z A E F ≤ E ⊓ A := by
    rw [hS.frame.sec2Z_eq]
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hZQ : sec2Z A E F ≤ Q := by
    intro w hw
    have h1 : w ∈ E ⊓ A ⊓ Q := by
      rw [h215ii]
      refine mem_inf.mpr ⟨?_, hZV hw⟩
      rw [← hZ2] at hw
      obtain ⟨x, hx, rfl⟩ := hw
      exact ⟨x, Subgroup.upperCentralSeries_mono _ (by norm_num) hx, rfl⟩
    exact h1.2
  have hNz : normalizer (Q : Set G) ≤ centralizer ({z} : Set G) := hQ.normalizer_le_centralizer
  have hKN : normalizer (Q : Set G) ≤ normalizer (Q : Set G) ⊓ centralizer ({z} : Set G) :=
    le_inf le_rfl hNz
  have hTN : sec2T E T₀ ≤ normalizer (Q : Set G) := hQ.T_le_normalizer
  have hMN : sec2M Q (sec2T E T₀) ≤ normalizer (Q : Set G) := sec2M_le_normalizer hTN
  have hKM : sec2M Q (sec2T E T₀) ≤ normalizer (Q : Set G) ⊓ centralizer ({z} : Set G) :=
    le_inf hMN (hMN.trans hNz)
  have hTM : sec2T E T₀ ≤ sec2M Q (sec2T E T₀) := le_sec2M Q _
  have hQM : Q ≤ sec2M Q (sec2T E T₀) := hQ.le.trans hTM
  have hHN : sec2H E F ≤ normalizer (Q : Set G) := le_sup_left.trans hQ.HT_le
  set ρN := rho hadd hsurj hker hKN with hρN
  set ρM := rho hadd hsurj hker hKM with hρM
  have hO : ∀ n, ρN n ∈ TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm :=
    rho_mem_orthogonalGroup hadd hsurj hker hKN hsq
  have hρ : ∀ m : ↥(sec2M Q (sec2T E T₀)), ρM m = ρN ⟨m, hMN m.2⟩ := fun m =>
    LinearEquiv.ext fun v => by
      obtain ⟨a, ha, rfl⟩ := hsurj v
      rw [rho_psi hadd hsurj hker hKM m ha, rho_psi hadd hsurj hker hKN _ ha]
  refine ⟨ψ, ρM, hadd, hsurj, hker, hsq, fun m a ha => (rho_psi hadd hsurj hker hKM m ha).symm,
    ?_, ?_⟩
  ·
    have : Finite ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) :=
      Finite.of_injective (fun f => (f : (Fin 6 → ZMod 2) → (Fin 6 → ZMod 2)))
        fun _ _ h => LinearEquiv.ext (congrFun h)
    have hHΩ : ∀ h (hh : h ∈ sec2H E F), ρN ⟨h, hHN hh⟩ ∈ timmesfeldOmega qMinus := fun h hh =>
      hQ.rho_mem_omega_of_mem_sec2H hadd hsurj hker hsq hKN h24 h26 hZQ hHN hh
    obtain ⟨t, htQ, hTH, W, hW64, hWQ, hWS, hWt⟩ := hQ.exists_t_of h21 h24 h26 h212
    have hTΩ : ∀ τ (hτ : τ ∈ sec2T E T₀), ρN ⟨τ, hTN hτ⟩ ∈ timmesfeldOmega qMinus := by
      intro τ hτ
      rcases hTH τ hτ with h | h
      · exact hHΩ τ h
      · have e : (⟨τ, hTN hτ⟩ : ↥(normalizer (Q : Set G))) =
            ⟨t, hQ.le.trans hTN htQ⟩⁻¹ * ⟨t * τ, hHN h⟩ := by
          apply Subtype.ext
          simp
        rw [e, map_mul, map_inv, hQ.rho_eq_one_of_mem hadd hsurj hker hKN htQ, inv_one, one_mul]
        exact hHΩ _ h
    have hMΩ : sec2M Q (sec2T E T₀) ≤
        ((timmesfeldOmega qMinus).comap ρN).map (normalizer (Q : Set G)).subtype := by
      refine iSup_le fun n => ?_
      intro x hx
      rw [mem_rightConjugate_iff] at hx
      have hxN : x ∈ normalizer (Q : Set G) := by
        have := mul_mem (mul_mem (inv_mem n.2) (hTN hx)) n.2
        simpa [mul_assoc] using this
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      have e : (⟨x, hxN⟩ : ↥(normalizer (Q : Set G))) =
          n⁻¹ * ⟨(n : G) * x * (n : G)⁻¹, hTN hx⟩ * n := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      show ρN ⟨x, hxN⟩ ∈ timmesfeldOmega qMinus
      rw [e, map_mul, map_mul, map_inv]
      have h1 := conj_mem_timmesfeldOmega (inv_mem (hO n)) (hTΩ _ hx)
      rwa [inv_inv] at h1
    have hHM : sec2H E F ≤ sec2M Q (sec2T E T₀) := by
      have hn : ((sec2M Q (sec2T E T₀)).subgroupOf (sec2H E F)).Normal :=
        ⟨fun x hx k => by
          rw [mem_subgroupOf] at hx ⊢
          have := conj_mem_sec2M (inv_mem (hHN k.2)) hx
          simpa using this⟩
      have hn' := hn.map C.φ C.surj
      rcases hn'.eq_bot_or_eq_top with hb | ht
      · exfalso
        obtain ⟨p, hp, hpS⟩ : ∃ p ∈ sec2P E, p ∉ sec2S A R E F := by
          by_contra hall
          push Not at hall
          have h1 : sec2S A R E F ⊓ sec2P E = sec2P E := inf_eq_right.mpr fun p hp => hall p hp
          rw [h1, hPE] at hSPE
          norm_num at hSPE
        have h1 : C.φ ⟨p, mem_sup_left hp⟩ ∈
            ((sec2M Q (sec2T E T₀)).subgroupOf (sec2H E F)).map C.φ :=
          ⟨⟨p, mem_sup_left hp⟩, hTM (le_sup_left.trans hPST hp), rfl⟩
        rw [hb, mem_bot] at h1
        have h2 : (⟨p, mem_sup_left hp⟩ : ↥(sec2H E F)) ∈ C.φ.ker := h1
        rw [C.ker] at h2
        exact hpS h2
      · intro h hh
        obtain ⟨m, hm, hmh⟩ : C.φ ⟨h, hh⟩ ∈
            ((sec2M Q (sec2T E T₀)).subgroupOf (sec2H E F)).map C.φ := by
          rw [ht]
          exact mem_top _
        have h1 : m⁻¹ * ⟨h, hh⟩ ∈ (sec2S A R E F).subgroupOf (sec2H E F) := by
          rw [← C.ker, MonoidHom.mem_ker, map_mul, map_inv, hmh, inv_mul_cancel]
        have e : h = (m : G) * ((m⁻¹ * ⟨h, hh⟩ : ↥(sec2H E F)) : G) := by simp
        rw [e]
        exact mul_mem hm (hTM (le_sup_right.trans hPST (mem_subgroupOf.mp h1)))
    obtain ⟨c, hc, w, hwZ, hcw⟩ := hQ.exists_mem_conj_not_mem_sec2Z h211N h212 h215
    have hcN : c ∈ normalizer (Q : Set G) := h215iii hc
    have hzZ := hQ.z_mem_Z h212
    have hwz : w ∉ zpowers z := by
      intro h
      apply hcw
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp h
      rw [conj_zpow_eq (mem_centralizer_singleton_iff.mp hc.2) k]
      exact hwZ
    have hwQ : w ∈ Q := hZQ hwZ
    have hp₀ : ψ w ≠ 0 := fun h => hwz ((hker w hwQ).mp h)
    have hq₀ : qMinus (ψ w) = 0 := (hsq w hwQ).mpr (hSp.elem w hwZ)
    have hHfix : ∀ h (hh : h ∈ sec2H E F), ρN ⟨h, hHN hh⟩ (ψ w) = ψ w := by
      intro h hh
      rw [rho_psi hadd hsurj hker hKN _ hwQ]
      have hhZ : h * w * h⁻¹ ∈ sec2Z A E F := by
        have h1 := Sec2.mem_normalizer_centerIn (hHS hh)
        rw [hZS] at h1
        exact (mem_normalizer_iff.mp h1 w).mp hwZ
      have hhz : h * w * h⁻¹ ∉ zpowers z := by
        intro h'
        apply hwz
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h'
        have e : w = h⁻¹ * (h * w * h⁻¹) * h := by group
        have h2 := conj_zpow_eq (mem_centralizer_singleton_iff.mp (inv_mem (hNz (hHN hh)))) k
        rw [inv_inv] at h2
        rw [e, ← hk, h2]
        exact zpow_mem (mem_zpowers z) k
      exact (psi_eq_iff hadd hker (hZQ hhZ) hwQ).mpr
        (mul_inv_mem_zpowers hQ.order hzZ hSp.card hhZ hwZ hhz hwz)
    have hcard := hQ.le_card_map_sec2H hadd hsurj hker hKN h24 h26 h212 hHN htQ hW64 hWQ hWS hWt
    set I := ((sec2H E F).subgroupOf (normalizer (Q : Set G))).map ρN with hI
    have hIΩ : I ≤ timmesfeldOmega qMinus := by
      rintro _ ⟨k, hk, rfl⟩
      exact hHΩ k hk
    have hstab : ∀ x ∈ timmesfeldOmega qMinus, x (ψ w) = ψ w → x ∈ I := by
      intro x hx hxp
      have hle : I.subgroupOf (timmesfeldOmega qMinus) ≤
          MulAction.stabilizer ↥(timmesfeldOmega qMinus) (ψ w) := by
        rintro ⟨_, hk⟩ ⟨k, hkH, rfl⟩
        rw [MulAction.mem_stabilizer_iff]
        exact hHfix k hkH
      have hcI : Nat.card (I.subgroupOf (timmesfeldOmega qMinus)) =
          Nat.card (MulAction.stabilizer ↥(timmesfeldOmega qMinus) (ψ w)) := by
        refine le_antisymm (Subgroup.card_le_of_le hle) ?_
        rw [Sec2Omega.card_stabilizer hp₀ hq₀, NXKernel.card_subgroupOf,
          inf_eq_left.mpr hIΩ]
        exact hcard
      have heq := Subgroup.eq_of_le_of_card_ge hle hcI.ge
      have h1 : (⟨x, hx⟩ : ↥(timmesfeldOmega qMinus)) ∈
          MulAction.stabilizer ↥(timmesfeldOmega qMinus) (ψ w) := hxp
      rw [← heq] at h1
      exact h1
    set Y := ((sec2M Q (sec2T E T₀)).subgroupOf (normalizer (Q : Set G))).map ρN with hY
    have hrange : ρM.range = Y := by
      ext x
      constructor
      · rintro ⟨m, rfl⟩
        exact ⟨⟨m, hMN m.2⟩, m.2, (hρ m).symm⟩
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨n, hn⟩, hρ ⟨n, hn⟩⟩
    rw [hrange]
    have hYΩ : Y ≤ timmesfeldOmega qMinus := by
      rintro _ ⟨n, hn, rfl⟩
      obtain ⟨n', hn', hnn'⟩ := hMΩ hn
      have : n' = n := Subtype.ext hnn'
      rw [← this]
      exact hn'
    have hIY : I ≤ Y := by
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨k, hHM hk, rfl⟩
    have hcY : ∀ x ∈ Y, ρN ⟨c, hcN⟩ * x * (ρN ⟨c, hcN⟩)⁻¹ ∈ Y := by
      rintro _ ⟨m, hm, rfl⟩
      have hm' : (m : G) ∈ sec2M Q (sec2T E T₀) := hm
      refine ⟨⟨c, hcN⟩ * m * ⟨c, hcN⟩⁻¹, mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
      have := conj_mem_sec2M (inv_mem hcN) hm'
      simpa using this
    set p₁ := ρN ⟨c, hcN⟩ (ψ w) with hp₁
    have hp₁e : p₁ = ψ (c * w * c⁻¹) := rho_psi hadd hsurj hker hKN _ hwQ
    have hcwQ : c * w * c⁻¹ ∈ Q := (mem_normalizer_iff.mp hcN w).mp hwQ
    have hne : ψ w ≠ p₁ := by
      rw [hp₁e]
      intro h
      apply hcw
      have h1 := (psi_eq_iff hadd hker hcwQ hwQ).mp h.symm
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
      have e : c * w * c⁻¹ = z ^ k * w := by rw [hk]; group
      rw [e]
      exact mul_mem (zpow_mem hzZ k) hwZ
    have hp₁0 : p₁ ≠ 0 := by
      rw [hp₁e]
      intro h
      apply hwz
      have h1 := (hker _ hcwQ).mp h
      have e : w = c⁻¹ * (c * w * c⁻¹) * c := by group
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
      have h2 := conj_zpow_eq (mem_centralizer_singleton_iff.mp (inv_mem hc.2)) k
      rw [inv_inv] at h2
      rw [e, ← hk, h2]
      exact zpow_mem (mem_zpowers z) k
    have hq₁ : qMinus p₁ = 0 := by
      rw [hp₁e, hsq _ hcwQ]
      calc c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
        _ = 1 := by rw [hSp.elem w hwZ]; group
    obtain ⟨x, hxΩ, hxp₁, hxp₀⟩ := Sec2Omega.exists_mem_fix_apply_ne hp₀ hq₀ hp₁0 hq₁ hne
    have hxY : x ∈ Y := by
      set r := ρN ⟨c, hcN⟩ with hr
      have h1 : r⁻¹ * x * r⁻¹⁻¹ ∈ timmesfeldOmega qMinus :=
        conj_mem_timmesfeldOmega (inv_mem (hO _)) hxΩ
      have h2 : (r⁻¹ * x * r⁻¹⁻¹) (ψ w) = ψ w := by
        rw [inv_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hp₁, hxp₁, hp₁,
          ← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id]
      have h3 := hcY _ (hIY (hstab _ h1 h2))
      have e : r * (r⁻¹ * x * r⁻¹⁻¹) * r⁻¹ = x := by group
      rwa [e] at h3
    exact Sec2Omega.eq_of_stabilizer_le hp₀ hq₀ hYΩ (fun x hx hxp => hIY (hstab x hx hxp))
      hxY hxp₀
  ·
    have hsyl := (hQ.sylow_zpowers_centralizer_of h24 h26 h212 hZQ).of_le
      (le_inf (zpowers_le.mpr (hQM hQ.z_mem_Q)) (zpowers_le.mpr hQ.z_mem_centralizer_Q))
      inf_le_right
    exact ker_rho_eq hQ.q8 hQ.centerIn_Q hQ.order hadd hsurj hker hsq hKM hQM hsyl

end CFSG.ComponentClassification.AS81
