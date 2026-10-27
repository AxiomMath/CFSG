module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NaturalSectionCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
import CFSG.CGT.PushingUpLit.BHS6.SymOffender
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltFixed
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.S11Parabolic
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FiveThreeBridge
import CFSG.GroupTheory.SwappedFactorsOffenders

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem theta_eq_one_of_centralizes_of_equivar {n : ℕ} (h3 : 3 ≤ n) {V M : Subgroup X}
    [hVn : V.Normal] {ψ : ↥V →* ↥(CFSG.Quasithin.G6.coreMod n)}
    (hψ : Function.Surjective ψ) {θ : ↥M →* Equiv.Perm (Fin n)}
    (he : ∀ (m : ↥M) (v : ↥V) (hv : (m : X) * v * (m : X)⁻¹ ∈ V),
      ψ ⟨(m : X) * v * (m : X)⁻¹, hv⟩ = CFSG.Quasithin.G6.coreAct n (θ m) (ψ v))
    {m : ↥M} (hm : ∀ v ∈ V, (m : X) * v * (m : X)⁻¹ = v) : θ m = 1 := by
  have hfix : CFSG.Quasithin.G6.coreAct n (θ m) = 1 := by
    refine MulEquiv.ext fun u => ?_
    obtain ⟨v, rfl⟩ := hψ u
    have hv : (m : X) * (v : X) * (m : X)⁻¹ ∈ V := hVn.conj_mem (v : X) v.2 (m : X)
    have h1 : (⟨(m : X) * (v : X) * (m : X)⁻¹, hv⟩ : ↥V) = v := Subtype.ext (hm (v : X) v.2)
    have h2 := he m v hv
    rw [h1] at h2
    show ((CFSG.Quasithin.G6.coreAct n) (θ m)) (ψ v) = ψ v
    exact h2.symm
  exact CFSG.CGT.PushingUpLit.BHS.coreAct_injective h3 (by rw [hfix, map_one])

private theorem sectionMap_ker_surjective {Q W L : Subgroup X} [⁅W, L⁆.Normal]
    {θ₀ : ↥(⊤ : Subgroup X) →* Equiv.Perm (Fin 11)}
    {ψ₀ : ↥⁅W, L⁆ →* ↥(CFSG.Quasithin.G6.coreMod 11)}
    (hψ₀s : Function.Surjective ψ₀)
    (hψ₀e : ∀ (m : ↥(⊤ : Subgroup X)) (w : ↥⁅W, L⁆)
        (hw : (m : X) * w * (m : X)⁻¹ ∈ ⁅W, L⁆),
      ψ₀ ⟨(m : X) * w * (m : X)⁻¹, hw⟩ = CFSG.Quasithin.G6.coreAct 11 (θ₀ m) (ψ₀ w))
    (hθ₀C : ∀ m : ↥(⊤ : Subgroup X), θ₀ m = 1 →
      (m : X) ∈ Subgroup.centralizer (W : Set X))
    (hQW : Q ≤ Subgroup.centralizer (W : Set X))
    (hCW : Subgroup.centralizer (W : Set X) = Q)
    (hVW : ⁅W, L⁆ ≤ W)
    (φ : X →* Equiv.Perm (Fin 11)) (hφ : Function.Surjective φ) (hker : φ.ker = Q) :
    θ₀.ker = Q.subgroupOf (⊤ : Subgroup X) ∧
      (θ₀.comp (Subgroup.topEquiv (G := X)).symm.toMonoidHom).ker = Q ∧
      Function.Surjective (θ₀.comp (Subgroup.topEquiv (G := X)).symm.toMonoidHom) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : X ≃* ↥(⊤ : Subgroup X) := (Subgroup.topEquiv (G := X)).symm
  have hθer : ∀ x : X, ((e x : ↥(⊤ : Subgroup X)) : X) = x :=
    fun x => Subgroup.topEquiv_symm_apply_coe x
  have hQker : Q.subgroupOf (⊤ : Subgroup X) ≤ θ₀.ker := by
    intro m hm
    rw [MonoidHom.mem_ker]
    refine theta_eq_one_of_centralizes_of_equivar (h3 := by norm_num) hψ₀s hψ₀e (fun v hv => ?_)
    have hmQ : (m : X) ∈ Q := hm
    have hvW : (v : X) ∈ W := hVW hv
    have hcomm : (v : X) * (m : X) = (m : X) * (v : X) :=
      Subgroup.mem_centralizer_iff.mp (hQW hmQ) (v : X) hvW
    calc (m : X) * (v : X) * (m : X)⁻¹ = ((v : X) * (m : X)) * (m : X)⁻¹ := by rw [hcomm]
      _ = (v : X) := by group
  have hker_le : θ₀.ker ≤ Q.subgroupOf (⊤ : Subgroup X) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf]
    have h2 : ((x : ↥(⊤ : Subgroup X)) : X) ∈ Subgroup.centralizer (W : Set X) := hθ₀C x hx
    rw [hCW] at h2
    exact h2
  have hθ₀ker : θ₀.ker = Q.subgroupOf (⊤ : Subgroup X) := le_antisymm hker_le hQker
  have hθker : (θ₀.comp e.toMonoidHom).ker = Q := by
    ext x
    show x ∈ (θ₀.comp e.toMonoidHom).ker ↔ x ∈ Q
    rw [show x ∈ (θ₀.comp e.toMonoidHom).ker ↔ (e x : ↥(⊤ : Subgroup X)) ∈ θ₀.ker from
      Iff.rfl, hθ₀ker, Subgroup.mem_subgroupOf]
    exact ⟨fun h => by rwa [hθer] at h, fun h => by rwa [hθer]⟩
  have hθs : Function.Surjective (θ₀.comp e.toMonoidHom) := by
    have hcard : Nat.card ↥(θ₀.comp e.toMonoidHom).range = Nat.card (Equiv.Perm (Fin 11)) := by
      rw [← Subgroup.index_ker (θ₀.comp e.toMonoidHom), hθker, ← hker, Subgroup.index_ker φ,
        MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top]
    rw [← MonoidHom.range_eq_top]
    refine Subgroup.eq_of_le_of_card_ge le_top ?_
    rw [hcard, Subgroup.card_top]
  exact ⟨hθ₀ker, hθker, hθs⟩

private theorem map_eq_alt_and_le_evenSub {L Q : Subgroup X} (hLn : L.Normal)
    (hLodd : L = Subgroup.closure {x : X | x ∈ L ∧ Odd (orderOf x)})
    {θ₀ : ↥(⊤ : Subgroup X) →* Equiv.Perm (Fin 11)}
    (hθker : (θ₀.comp (Subgroup.topEquiv (G := X)).symm.toMonoidHom).ker = Q)
    (hθs : Function.Surjective (θ₀.comp (Subgroup.topEquiv (G := X)).symm.toMonoidHom))
    (hθ₀A : ∀ σ ∈ alternatingGroup (Fin 11), ∃ l ∈ L, ∃ hl : l ∈ ⊤, θ₀ ⟨l, hl⟩ = σ) :
    L.map (θ₀.comp (Subgroup.topEquiv (G := X)).symm.toMonoidHom) = alternatingGroup (Fin 11) ∧
      L ≤ CFSG.CGT.PushingUpLit.BHS6.evenSub (⊤ : Subgroup X) θ₀ ∧
      CFSG.CGT.PushingUpLit.BHS6.evenSub (⊤ : Subgroup X) θ₀ ≤ L ⊔ Q := by
  classical
  let e : X ≃* ↥(⊤ : Subgroup X) := (Subgroup.topEquiv (G := X)).symm
  let θ : X →* Equiv.Perm (Fin 11) := θ₀.comp e.toMonoidHom
  have hθ₀s : Function.Surjective θ₀ := by
    intro σ
    obtain ⟨x, hx⟩ := hθs σ
    exact ⟨e x, hx⟩
  have hLalt : L.map θ = alternatingGroup (Fin 11) := by
    refine map_eq_alternatingGroup_of_closure_odd (n := 11) (by norm_num) hLn hLodd θ hθs ?_
    intro hle
    haveI : Nontrivial ↥(alternatingGroup (Fin 11)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp)
    obtain ⟨σ, hσ⟩ := exists_ne (1 : ↥(alternatingGroup (Fin 11)))
    obtain ⟨l, hlL, hl, hval⟩ := hθ₀A σ σ.2
    have hmem : θ l = 1 := hle hlL
    have h1 : θ l = θ₀ ⟨l, hl⟩ := rfl
    rw [h1, hval] at hmem
    exact hσ (Subtype.ext hmem)
  have hLE₀ : L ≤ CFSG.CGT.PushingUpLit.BHS6.evenSub (⊤ : Subgroup X) θ₀ := by
    intro l hl
    refine CFSG.CGT.PushingUpLit.BHS6.mem_evenSub.mpr ⟨Subgroup.mem_top l, ?_⟩
    have h1 : θ l ∈ L.map θ := Subgroup.mem_map_of_mem θ hl
    rw [hLalt] at h1
    have h2 : θ l = θ₀ ⟨l, Subgroup.mem_top l⟩ := rfl
    rwa [h2] at h1
  have hE₀LQ : CFSG.CGT.PushingUpLit.BHS6.evenSub (⊤ : Subgroup X) θ₀ ≤ L ⊔ Q := by
    intro x hx
    obtain ⟨hxG, hxA⟩ := CFSG.CGT.PushingUpLit.BHS6.mem_evenSub.mp hx
    have h1 : θ x ∈ L.map θ := by
      rw [hLalt]
      have h2 : θ x = θ₀ ⟨x, hxG⟩ := rfl
      rwa [h2]
    obtain ⟨l, hlL, hl⟩ := Subgroup.mem_map.mp h1
    have hmemker : x * l⁻¹ ∈ Q := by
      have h3 : θ (x * l⁻¹) = 1 := by
        rw [map_mul, map_inv, hl, mul_inv_cancel]
      exact hθker ▸ (MonoidHom.mem_ker.mpr h3)
    have hxeq : x = (x * l⁻¹) * l := by group
    rw [hxeq, sup_comm]
    exact Subgroup.mul_mem_sup hmemker hlL
  exact ⟨hLalt, hLE₀, hE₀LQ⟩

private theorem psi'_ker_eq {L Q W W' E₀ : Subgroup X}
    {ψ₀ : ↥⁅W, L⁆ →* ↥(CFSG.Quasithin.G6.coreMod 11)}
    (hW'V : W' ≤ ⁅W, L⁆) (hW'le : W' ≤ W)
    (hψ₀k : ψ₀.ker = (⁅W, L⁆ ⊓ Subgroup.centralizer (L : Set X)).subgroupOf ⁅W, L⁆)
    (hQeqW : W ≤ Subgroup.centralizer (Q : Set X))
    (hLE₀ : L ≤ E₀) (hE₀LQ : E₀ ≤ L ⊔ Q) :
    (ψ₀.comp (Subgroup.inclusion hW'V)).ker =
      (W' ⊓ Subgroup.centralizer (E₀ : Set X)).subgroupOf W' := by
  classical
  ext w
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker]
  constructor
  · intro hw
    have h1 : (⟨(w : X), hW'V w.2⟩ : ↥⁅W, L⁆) ∈ ψ₀.ker := hw
    rw [hψ₀k, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h1
    refine ⟨w.2, ?_⟩
    have hL : (w : X) ∈ Subgroup.centralizer (L : Set X) := h1.2
    have hQ : (w : X) ∈ Subgroup.centralizer (Q : Set X) := hQeqW (hW'le w.2)
    have hsup : (w : X) ∈ Subgroup.centralizer ((L ⊔ Q : Subgroup X) : Set X) := by
      rw [CFSG.GroupTheory.centralizer_sup_eq_inf_centralizer]
      exact ⟨hL, hQ⟩
    exact Subgroup.centralizer_le (fun y hy => hE₀LQ hy) hsup
  · rintro ⟨-, hwC⟩
    have h1 : (w : X) ∈ Subgroup.centralizer (L : Set X) :=
      Subgroup.centralizer_le (fun y hy => hLE₀ hy) hwC
    have h2 : (⟨(w : X), hW'V w.2⟩ : ↥⁅W, L⁆) ∈ ψ₀.ker := by
      rw [hψ₀k, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨hW'V w.2, h1⟩
    exact h2

private theorem centralizer_eq_pCoreOf {L Q E₀ W' : Subgroup X} [W'.Normal]
    {θ : X →* Equiv.Perm (Fin 11)} (hθker : θ.ker = Q) (hθs : Function.Surjective θ)
    (hLalt : L.map θ = alternatingGroup (Fin 11)) (hQleC : Q ≤ Subgroup.centralizer (W' : Set X))
    (hE₀LQ : E₀ ≤ L ⊔ Q) (hW'perf : ⁅E₀, W'⁆ = W') (hW'ne : W' ≠ ⊥) :
    Subgroup.centralizer (W' : Set X) = Q := by
  classical
  refine le_antisymm ?_ hQleC
  by_contra hcon
  haveI hCn : (Subgroup.centralizer (W' : Set X)).Normal := Subgroup.normal_centralizer
  have hne : Subgroup.map θ (Subgroup.centralizer (W' : Set X)) ≠ ⊥ := by
    intro hbot
    apply hcon
    intro x hx
    have hx' : θ x = 1 := by
      have hmem : θ x ∈ Subgroup.map θ (Subgroup.centralizer (W' : Set X)) :=
        Subgroup.mem_map_of_mem θ hx
      rw [hbot] at hmem
      simpa using hmem
    exact hθker ▸ (MonoidHom.mem_ker.mpr hx')
  haveI hmapN : (Subgroup.map θ (Subgroup.centralizer (W' : Set X))).Normal :=
    Subgroup.Normal.map (Subgroup.normal_centralizer) θ hθs
  have hAltle : alternatingGroup (Fin 11) ≤ Subgroup.map θ (Subgroup.centralizer (W' : Set X)) :=
    Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 11) (by simp)
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hne)
  have hLC : L ≤ Subgroup.centralizer (W' : Set X) := by
    intro l hl
    have h1 : θ l ∈ Subgroup.map θ (Subgroup.centralizer (W' : Set X)) :=
      hAltle (hLalt ▸ Subgroup.mem_map_of_mem θ hl)
    obtain ⟨c, hcC, hc⟩ := Subgroup.mem_map.mp h1
    have h2 : l * c⁻¹ ∈ Q := by
      have h3 : θ (l * c⁻¹) = 1 := by
        rw [map_mul, map_inv, hc, mul_inv_cancel]
      exact hθker ▸ (MonoidHom.mem_ker.mpr h3)
    have h3 : l = (l * c⁻¹) * c := by group
    rw [h3]
    exact mul_mem (hQleC h2) hcC
  have hE₀C : E₀ ≤ Subgroup.centralizer (W' : Set X) :=
    hE₀LQ.trans (sup_le hLC hQleC)
  have hcomm : ⁅E₀, W'⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hE₀C
  rw [hcomm] at hW'perf
  exact hW'ne hW'perf.symm

private theorem exists_altNatData_of_perfectCore {L Q W W' E₀ : Subgroup X} [W'.Normal]
    [hVn : ⁅W, L⁆.Normal]
    {θ₀ : ↥(⊤ : Subgroup X) →* Equiv.Perm (Fin 11)}
    {ψ₀ : ↥⁅W, L⁆ →* ↥(CFSG.Quasithin.G6.coreMod 11)}
    (hW'V : W' ≤ ⁅W, L⁆)
    (hE₀ : E₀ = CFSG.CGT.PushingUpLit.BHS6.evenSub (⊤ : Subgroup X) θ₀)
    (hW'e : IsElemAbelian 2 W') (hW'N : ⊤ ≤ Subgroup.normalizer (W' : Set X))
    (hθ₀s : Function.Surjective θ₀) (hθ₀ker : θ₀.ker = Q.subgroupOf (⊤ : Subgroup X))
    (hCW' : Subgroup.centralizer (W' : Set X) = Q)
    (hψ's : Function.Surjective (ψ₀.comp (Subgroup.inclusion hW'V)))
    (hψ'k : (ψ₀.comp (Subgroup.inclusion hW'V)).ker =
      (W' ⊓ Subgroup.centralizer (E₀ : Set X)).subgroupOf W')
    (hW'perf : ⁅E₀, W'⁆ = W')
    (hψ₀e : ∀ (m : ↥(⊤ : Subgroup X)) (w : ↥⁅W, L⁆)
        (hw : (m : X) * w * (m : X)⁻¹ ∈ ⁅W, L⁆),
      ψ₀ ⟨(m : X) * w * (m : X)⁻¹, hw⟩ = CFSG.Quasithin.G6.coreAct 11 (θ₀ m) (ψ₀ w)) :
    letI : CommGroup ↥W' := commGroupOfElemAbelian hW'e
    ∃ D : CFSG.CGT.PushingUpLit.BHS.AltNatData (CFSG.Quasithin.autOn E₀ W') 11,
      ∀ w : ↥W', D.β w = (ψ₀.comp (Subgroup.inclusion hW'V)) w := by
  classical
  let _ : CommGroup ↥W' := commGroupOfElemAbelian hW'e
  subst hE₀
  have hE : CFSG.CGT.PushingUpLit.BHS6.evenSub (⊤ : Subgroup X) θ₀ ≤
      Subgroup.normalizer (W' : Set X) := fun x _ => hW'N (Subgroup.mem_top x)
  have hφ'E : Function.Surjective (CFSG.CGT.PushingUpLit.BHS6.evenHom (⊤ : Subgroup X) θ₀) :=
    CFSG.CGT.PushingUpLit.BHS6.evenHom_surjective (⊤ : Subgroup X) θ₀ hθ₀s
  have hφ'k : (CFSG.CGT.PushingUpLit.BHS6.evenHom (⊤ : Subgroup X) θ₀).ker =
      (CFSG.CGT.PushingUpLit.BHS6.evenSub (⊤ : Subgroup X) θ₀ ⊓
        Subgroup.centralizer (W' : Set X)).subgroupOf
          (CFSG.CGT.PushingUpLit.BHS6.evenSub (⊤ : Subgroup X) θ₀) := by
    have hcoe : ∀ x : ↥(CFSG.CGT.PushingUpLit.BHS6.evenSub (⊤ : Subgroup X) θ₀),
        ((CFSG.CGT.PushingUpLit.BHS6.evenHom (⊤ : Subgroup X) θ₀ x :
          ↥(alternatingGroup (Fin 11))) : Equiv.Perm (Fin 11)) =
        θ₀ ⟨(x : X), CFSG.CGT.PushingUpLit.BHS6.evenSub_le (⊤ : Subgroup X) θ₀ x.2⟩ :=
      fun x => CFSG.CGT.PushingUpLit.BHS6.evenHom_coe (⊤ : Subgroup X) θ₀ x
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have h1 : θ₀ ⟨(x : X),
          CFSG.CGT.PushingUpLit.BHS6.evenSub_le (⊤ : Subgroup X) θ₀ x.2⟩ = 1 := by
        rw [← hcoe x]
        exact congrArg Subtype.val hx
      have h2 : (⟨(x : X),
          CFSG.CGT.PushingUpLit.BHS6.evenSub_le (⊤ : Subgroup X) θ₀ x.2⟩ :
          ↥(⊤ : Subgroup X)) ∈ θ₀.ker := h1
      rw [hθ₀ker, Subgroup.mem_subgroupOf] at h2
      rw [hCW']
      exact h2
    · rintro ⟨-, hxW⟩
      apply Subtype.ext
      rw [hcoe x]
      have h1 : ((x : ↥(CFSG.CGT.PushingUpLit.BHS6.evenSub (⊤ : Subgroup X) θ₀)) : X) ∈ Q := by
        rw [← hCW']; exact hxW
      have h2 : (⟨((x : ↥(CFSG.CGT.PushingUpLit.BHS6.evenSub (⊤ : Subgroup X) θ₀)) : X),
          Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup X)) ∈ θ₀.ker := by
        rw [hθ₀ker, Subgroup.mem_subgroupOf]
        exact h1
      rw [MonoidHom.mem_ker] at h2
      exact h2
  have hψ'coe : ∀ w : ↥W',
      (ψ₀.comp (Subgroup.inclusion hW'V)) w = ψ₀ ⟨(w : X), hW'V w.2⟩ := by
    intro w
    show ψ₀ ((Subgroup.inclusion hW'V) w) = ψ₀ ⟨(w : X), hW'V w.2⟩
    rw [show (Subgroup.inclusion hW'V) w = ⟨(w : X), hW'V w.2⟩ from Subtype.ext rfl]
  exact CFSG.CGT.PushingUpLit.BHS6.exists_altNatData_of_data (Γ := X) (W := W')
    (E := CFSG.CGT.PushingUpLit.BHS6.evenSub (⊤ : Subgroup X) θ₀) (n := 11) hW'e hE hW'perf
    (CFSG.CGT.PushingUpLit.BHS6.evenHom (⊤ : Subgroup X) θ₀)
    (ψ₀.comp (Subgroup.inclusion hW'V)) hφ'E hφ'k hψ's hψ'k (by
      intro ee w hw
      rw [hψ'coe ⟨(ee : X) * (w : X) * (ee : X)⁻¹, hw⟩, hψ'coe w]
      have h2 : ((CFSG.CGT.PushingUpLit.BHS6.evenHom (⊤ : Subgroup X) θ₀ ee :
          ↥(alternatingGroup (Fin 11))) : Equiv.Perm (Fin 11)) =
          θ₀ ⟨(ee : X), Subgroup.mem_top _⟩ :=
        CFSG.CGT.PushingUpLit.BHS6.evenHom_coe (⊤ : Subgroup X) θ₀ ee
      rw [h2]
      exact hψ₀e ⟨(ee : X), Subgroup.mem_top _⟩ ⟨(w : X), hW'V w.2⟩
        (hVn.conj_mem (w : X) (hW'V w.2) (ee : X)))

private theorem ker_eq_bot_of_altNatData {W : Type} [CommGroup W] [Finite W] {n : ℕ}
    (hW2 : ∀ w : W, w ^ 2 = 1) (hodd : Odd n) (h7 : 7 ≤ n) {E : Subgroup (MulAut W)}
    (D : CFSG.CGT.PushingUpLit.BHS.AltNatData E n) (ψ : W →* ↥(CFSG.Quasithin.G6.coreMod n))
    (hψs : Function.Surjective ψ) (hDβ : ∀ w, D.β w = ψ w) : ψ.ker = ⊥ := by
  let f : W ⧸ ψ.ker →* ↥(CFSG.Quasithin.G6.coreMod n) := QuotientGroup.kerLift ψ
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨w, hw⟩ := hψs y
    refine ⟨QuotientGroup.mk w, ?_⟩
    change QuotientGroup.kerLift ψ (QuotientGroup.mk w) = y
    rw [QuotientGroup.kerLift_mk, hw]
  let e : W ⧸ ψ.ker ≃* ↥(CFSG.Quasithin.G6.coreMod n) :=
    MulEquiv.ofBijective f ⟨QuotientGroup.kerLift_injective ψ, hfs⟩
  have he : ∀ w : W, e (QuotientGroup.mk w) = ψ w := by
    intro w
    change QuotientGroup.kerLift ψ (QuotientGroup.mk w) = ψ w
    rw [QuotientGroup.kerLift_mk]
  have hU : ∀ γ : ↥E, ∀ u ∈ ψ.ker, (Subgroup.subtype E) γ u = u := by
    intro γ u hu
    have h1 : D.β u = 1 := by rw [hDβ]; exact hu
    have h2 : u ∈ CFSG.Quasithin.fixV E := D.ker_fix u h1
    exact (CFSG.Quasithin.mem_fixV.mp h2) γ γ.2
  have hρA : ∀ γ : ↥E,
      ((alternatingGroup (Fin n)).subtype.comp D.θ.toMonoidHom) γ ∈ alternatingGroup (Fin n) :=
    fun γ => (D.θ γ).2
  have hρs : ∀ σ ∈ alternatingGroup (Fin n),
      ∃ γ, ((alternatingGroup (Fin n)).subtype.comp D.θ.toMonoidHom) γ = σ := by
    intro σ hσ
    obtain ⟨γ, hγ⟩ := D.θ.surjective ⟨σ, hσ⟩
    exact ⟨γ, congrArg Subtype.val hγ⟩
  have hρi : Function.Injective ((alternatingGroup (Fin n)).subtype.comp D.θ.toMonoidHom) := by
    intro a b hab
    exact D.θ.injective (Subtype.ext hab)
  have hge : ∀ (γ : ↥E) (w : W),
      e (QuotientGroup.mk ((Subgroup.subtype E) γ w)) =
        CFSG.Quasithin.G6.coreAct n
          (((alternatingGroup (Fin n)).subtype.comp D.θ.toMonoidHom) γ)
          (e (QuotientGroup.mk w)) := by
    intro γ w
    rw [he w, he ((Subgroup.subtype E) γ w), ← hDβ, ← hDβ]
    exact D.equivar γ w
  have hgen : Subgroup.closure {x : W | ∃ γ w, x = (Subgroup.subtype E) γ w * w⁻¹} = ⊤ := by
    rw [← D.comm_top]
    congr 1
    ext w
    constructor
    · rintro ⟨γ, w', rfl⟩
      exact ⟨(γ : MulAut W), γ.2, w', rfl⟩
    · rintro ⟨x, hx, w', rfl⟩
      exact ⟨⟨x, hx⟩, w', rfl⟩
  exact CFSG.Quasithin.B69K.fixed_eq_bot_of_natural (W := W) hW2 (Subgroup.subtype E)
    (U := ψ.ker) hU hodd h7 ((alternatingGroup (Fin n)).subtype.comp D.θ.toMonoidHom)
    hρA hρs hρi e hge hgen

private theorem perfectCore_ne_bot {W' : Subgroup X}
    {ψ' : ↥W' →* ↥(CFSG.Quasithin.G6.coreMod 11)}
    (hψ's : Function.Surjective ψ') : W' ≠ ⊥ := by
  intro hbot
  have hcard : 1 < Nat.card ↥(CFSG.Quasithin.G6.coreMod 11) := by
    have h := CFSG.CGT.PushingUpLit.BHS.card_coreMod_mul_two (n := 11) (by norm_num : Odd 11)
    have h2 : (2 : ℕ) ^ 11 = 2048 := by norm_num
    rw [h2] at h
    nlinarith [Nat.card_pos (α := ↥(CFSG.Quasithin.G6.coreMod 11))]
  have h1 : Nat.card ↥(CFSG.Quasithin.G6.coreMod 11) ≤ Nat.card ↥W' :=
    Nat.card_le_card_of_surjective ψ' hψ's
  rw [hbot, Subgroup.card_bot] at h1
  omega

private theorem isNatSym_of_perfectCore {L Q W W' E₀ : Subgroup X} [hVn : ⁅W, L⁆.Normal]
    {θ₀ : ↥(⊤ : Subgroup X) →* Equiv.Perm (Fin 11)}
    {ψ₀ : ↥⁅W, L⁆ →* ↥(CFSG.Quasithin.G6.coreMod 11)}
    (hW'V : W' ≤ ⁅W, L⁆)
    (hθ₀s : Function.Surjective θ₀) (hθ₀ker : θ₀.ker = Q.subgroupOf (⊤ : Subgroup X))
    (hCW' : Subgroup.centralizer (W' : Set X) = Q)
    (hψ's : Function.Surjective (ψ₀.comp (Subgroup.inclusion hW'V)))
    (hψ'k : (ψ₀.comp (Subgroup.inclusion hW'V)).ker =
      (W' ⊓ Subgroup.centralizer (E₀ : Set X)).subgroupOf W')
    (hkerbot : (ψ₀.comp (Subgroup.inclusion hW'V)).ker = ⊥)
    (hψ₀e : ∀ (m : ↥(⊤ : Subgroup X)) (w : ↥⁅W, L⁆)
        (hw : (m : X) * w * (m : X)⁻¹ ∈ ⁅W, L⁆),
      ψ₀ ⟨(m : X) * w * (m : X)⁻¹, hw⟩ = CFSG.Quasithin.G6.coreAct 11 (θ₀ m) (ψ₀ w)) :
    CFSG.CGT.PushingUpLit.BHS.IsNatSym (⊤ : Subgroup X) W' 11 := by
  classical
  have hψ'coe : ∀ w : ↥W',
      (ψ₀.comp (Subgroup.inclusion hW'V)) w = ψ₀ ⟨(w : X), hW'V w.2⟩ := by
    intro w
    show ψ₀ ((Subgroup.inclusion hW'V) w) = ψ₀ ⟨(w : X), hW'V w.2⟩
    rw [show (Subgroup.inclusion hW'V) w = ⟨(w : X), hW'V w.2⟩ from Subtype.ext rfl]
  refine ⟨θ₀, ψ₀.comp (Subgroup.inclusion hW'V), hθ₀s, ?_, hψ's, ?_, ?_⟩
  · rw [top_inf_eq, hCW', hθ₀ker]
  · rw [hkerbot]
    refine le_antisymm bot_le ?_
    intro w hw
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hw
    have h1 : w ∈ (ψ₀.comp (Subgroup.inclusion hW'V)).ker := by
      rw [hψ'k, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨hw.1, Subgroup.centralizer_le (fun x _ => Subgroup.mem_top x) hw.2⟩
    rwa [hkerbot, Subgroup.mem_bot] at h1
  · intro m v hv
    rw [hψ'coe ⟨_, hv⟩, hψ'coe v]
    exact hψ₀e m ⟨(v : X), hW'V v.2⟩ (hVn.conj_mem (v : X) (hW'V v.2) (m : X))

private theorem transport_sym_swap_data {Q W' T : Subgroup X}
    {φ'' : ↥(⊤ : Subgroup X) →* Equiv.Perm (Fin 11)} {T' : Set (Equiv.Perm (Fin 11))}
    (hφ''s : Function.Surjective φ'')
    (hφ''k : φ''.ker = (⊤ ⊓ Subgroup.centralizer (W' : Set X)).subgroupOf (⊤ : Subgroup X))
    (hCW' : Subgroup.centralizer (W' : Set X) = Q)
    (hT's : ∀ t ∈ T', t.IsSwap)
    (hT'eq : ((CFSG.Quasithin.baum T).subgroupOf (⊤ : Subgroup X)).map φ'' =
      Subgroup.closure T') :
    ∃ θ : X →* Equiv.Perm (Fin 11), Function.Surjective θ ∧ θ.ker = Q ∧
      (∀ t ∈ T', t.IsSwap) ∧ (CFSG.Quasithin.baum T).map θ = Subgroup.closure T' := by
  classical
  let e : X ≃* ↥(⊤ : Subgroup X) := (Subgroup.topEquiv (G := X)).symm
  refine ⟨φ''.comp e.toMonoidHom, hφ''s.comp e.surjective, ?_, hT's, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker]
    change φ'' (e x) = 1 ↔ x ∈ Q
    have h1 : (e x : ↥(⊤ : Subgroup X)) ∈
        (⊤ ⊓ Subgroup.centralizer (W' : Set X)).subgroupOf (⊤ : Subgroup X) ↔
        x ∈ Subgroup.centralizer (W' : Set X) := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.topEquiv_symm_apply_coe]
      exact ⟨fun h => h.2, fun h => ⟨Subgroup.mem_top x, h⟩⟩
    rw [← MonoidHom.mem_ker (f := φ'') (x := e x), hφ''k, h1, hCW']
  · have hmap : (CFSG.Quasithin.baum T).map (φ''.comp e.toMonoidHom) =
        ((CFSG.Quasithin.baum T).subgroupOf (⊤ : Subgroup X)).map φ'' := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨e x, Subgroup.mem_subgroupOf.mpr (by rwa [Subgroup.topEquiv_symm_apply_coe]), rfl⟩
      · rintro ⟨m, hm, rfl⟩
        refine ⟨(m : X), ?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.mp hm
        · show φ'' (e (m : X)) = φ'' m
          rw [show e (m : X) = m from
            Subtype.ext (Subgroup.topEquiv_symm_apply_coe (m : X))]
    rw [hmap, hT'eq]

theorem exists_map_baum_eq_closure_swaps {L T : Subgroup X}
    (hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup X)) (hLn : L.Normal)
    (hLodd : L = Subgroup.closure {x : X | x ∈ L ∧ Odd (orderOf x)})
    (φ : X →* Equiv.Perm (Fin 11)) (hφ : Function.Surjective φ)
    (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    (hCeq : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnC T =
      CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hJ : ¬ CFSG.Quasithin.thompsonJ T ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hnat : NaturalSectionOn (CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnV T) L ⊤
      11) :
    ∃ θ : X →* Equiv.Perm (Fin 11), Function.Surjective θ ∧
      θ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ∧
      ∃ T' : Set (Equiv.Perm (Fin 11)), (∀ t ∈ T', t.IsSwap) ∧
        (CFSG.Quasithin.baum T).map θ = Subgroup.closure T' := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ₀, ψ₀, hψ₀s, hψ₀k, hθ₀A, hθ₀C, hψ₀e⟩ :=
    exists_coreMod_of_naturalSectionOn (X := X) (W := gnV T) (L := L) (M := ⊤) (n := 11)
      (by norm_num) hnat
  have hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T := hT.pCoreOf_le
  have hQW : pCoreOf 2 (⊤ : Subgroup X) ≤ gnC T :=
    CFSG.AGLEmbeddingD2.GN.pCoreOf_le_gnC_of_le hQT
  have hWQ : gnV T ≤ pCoreOf 2 (⊤ : Subgroup X) :=
    CFSG.AGLEmbeddingD2.GN.gnV_le_pCoreOf_of_le hC hQT
  have hQeqW : gnV T ≤ Subgroup.centralizer (pCoreOf 2 (⊤ : Subgroup X) : Set X) :=
    Subgroup.le_centralizer_iff.mp hQW
  haveI hWn : (gnV T).Normal := CFSG.AGLEmbeddingD2.GN.normal_gnV T
  haveI hVn : (⁅gnV T, L⁆).Normal := Subgroup.commutator_normal _ _
  have hVW : ⁅gnV T, L⁆ ≤ gnV T := Subgroup.commutator_le_left _ _
  have hWe : IsElemAbelian 2 (gnV T) :=
    CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.isElemAbelian_gnV_of_le hC hQT
  let e : X ≃* ↥(⊤ : Subgroup X) := (Subgroup.topEquiv (G := X)).symm
  let θ : X →* Equiv.Perm (Fin 11) := θ₀.comp e.toMonoidHom
  obtain ⟨hθ₀ker, hθker, hθs⟩ :=
    sectionMap_ker_surjective hψ₀s hψ₀e hθ₀C hQW hCeq hVW φ hφ hker
  have hθ₀s : Function.Surjective θ₀ := by
    intro σ
    obtain ⟨x, hx⟩ := hθs σ
    exact ⟨e x, hx⟩
  obtain ⟨hLalt, hLE₀, hE₀LQ⟩ := map_eq_alt_and_le_evenSub hLn hLodd hθker hθs hθ₀A
  obtain ⟨W', hW'V, hW'N, hW'ψ, hW'perf⟩ :=
    CFSG.CGT.PushingUpLit.BHS6.exists_perfectCore (Γ := X) (n := 11) (G := (⊤ : Subgroup X))
      (V := ⁅gnV T, L⁆) (Subgroup.le_normalizer_of_normal (H := ⁅gnV T, L⁆) (K := ⊤))
      (by norm_num) θ₀ hθ₀s ψ₀ hψ₀s hψ₀e
  have hW'le : W' ≤ gnV T := hW'V.trans hVW
  let ψ' : ↥W' →* ↥(CFSG.Quasithin.G6.coreMod 11) := ψ₀.comp (Subgroup.inclusion hW'V)
  have hψ's : Function.Surjective ψ' := by
    intro u
    obtain ⟨w, hwW, hwu⟩ := hW'ψ u
    refine ⟨⟨(w : X), hwW⟩, ?_⟩
    show ψ₀ (Subgroup.inclusion hW'V ⟨(w : X), hwW⟩) = u
    rw [show Subgroup.inclusion hW'V ⟨(w : X), hwW⟩ = w from Subtype.ext rfl]
    exact hwu
  have hW'e : IsElemAbelian 2 W' := CFSG.CGT.PushingUpLit.BHS.isElemAbelian_of_le' hW'le hWe
  letI : CommGroup ↥W' := commGroupOfElemAbelian hW'e
  have hW'2 : ∀ w : ↥W', w ^ 2 = 1 := fun w => Subtype.ext (by simpa [sq] using hW'e.2 w w.2)
  haveI hW'n : W'.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hW'N)
  have hW'ne : W' ≠ ⊥ := perfectCore_ne_bot hψ's
  have hQleC : pCoreOf 2 (⊤ : Subgroup X) ≤ Subgroup.centralizer (W' : Set X) :=
    hQW.trans (Subgroup.centralizer_le (fun x hx => hW'le hx))
  have hCW' : Subgroup.centralizer (W' : Set X) = pCoreOf 2 (⊤ : Subgroup X) :=
    centralizer_eq_pCoreOf hθker hθs hLalt hQleC hE₀LQ hW'perf hW'ne
  have hψ'k : ψ'.ker =
      (W' ⊓ Subgroup.centralizer (CFSG.CGT.PushingUpLit.BHS6.evenSub (⊤ : Subgroup X) θ₀ :
        Set X)).subgroupOf W' :=
    psi'_ker_eq hW'V hW'le hψ₀k hQeqW hLE₀ hE₀LQ
  obtain ⟨D, hDβ⟩ :=
    exists_altNatData_of_perfectCore hW'V rfl hW'e hW'N hθ₀s hθ₀ker hCW' hψ's hψ'k hW'perf hψ₀e
  have hkerbot : ψ'.ker = ⊥ :=
    ker_eq_bot_of_altNatData hW'2 (by norm_num) (by norm_num) D ψ' hψ's hDβ
  have hnat' : CFSG.CGT.PushingUpLit.BHS.IsNatSym (⊤ : Subgroup X) W' 11 :=
    isNatSym_of_perfectCore hW'V hθ₀s hθ₀ker hCW' hψ's hψ'k hkerbot hψ₀e
  have hW'Q : W' ≤ omegaOneCenterOf (pCoreOf 2 (⊤ : Subgroup X)) := by
    intro x hx
    exact Subgroup.subset_closure ⟨⟨hWQ (hW'le hx), hQeqW (hW'le hx)⟩, hW'e.2 x hx⟩
  have hJ' : ¬ thompsonJ T ≤ Subgroup.centralizer (W' : Set X) := by
    rw [hCW']
    exact hJ
  obtain ⟨φ'', ψ'', hφ''s, hφ''k, -, -, -, T', -, hT's, -, hT'eq⟩ :=
    CFSG.CGT.PushingUpLit.BHS6.sym_swap_data (Γ := X) (G := (⊤ : Subgroup X)) (T := T)
      (V := W') (m := 5) (by norm_num) hT hW'N hW'Q hJ' hnat'
  obtain ⟨θfin, hθfin_s, hθfin_k, -, hT'eq'⟩ :=
    transport_sym_swap_data hφ''s hφ''k hCW' hT's hT'eq
  exact ⟨θfin, hθfin_s, hθfin_k, T', hT's, hT'eq'⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
