module

public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.LocalAnalysis.GLTheoremA.S10.StrongCover
public import CFSG.LocalAnalysis.GLTheoremA.Prop51
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxClaim
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs710
public import CFSG.LocalAnalysis.GLTheoremA.S12.Diag
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop122B

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

theorem isKGroup_le_cx (h : Cfg12 G m p B x L D K) {d : G} (hd1 : d ≠ 1) {M : Subgroup G}
    (hM : M ≤ Subgroup.centralizer ({d} : Set G)) : CFSG.Open.IsKGroup ↥M :=
  (kGroup_centralizer h.ctx.toS6 hd1).of_injective (Subgroup.inclusion hM) (Subgroup.inclusion_injective hM)

theorem comm_primeCore_le_core (M : Subgroup G) : (⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p M := by
  rw [Subgroup.commutator_le]
  intro m hm o ho
  have hn : m ∈ Subgroup.normalizer (GLAPPrimeCoreOf p M : Set G) := normalizer_le_normalizer_glaPPrimeCoreOf p M
    (Subgroup.le_normalizer hm)
  have h1 : m * o * m⁻¹ ∈ GLAPPrimeCoreOf p M := (Subgroup.mem_normalizer_iff.1 hn o).1 ho
  have h2 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ ho)
  simpa [commutatorElement_def] using h2

theorem exists_invariant_sylow_comm (hp : p.Prime) (hp2 : p ≠ 2) {X M B' : Subgroup G} (hM : GLAPComponent p X M)
    (hB : IsElemAbelian p B') (hBM : B' ≤ Subgroup.normalizer (M : Set G)) :
    ∃ U : Subgroup G, U ≤ ⁅M, GLAPPrimeCoreOf p M⁆ ∧ IsPGroup 2 U ∧
      ¬ 2 ∣ U.relIndex (⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G) ∧ B' ≤ Subgroup.normalizer (U : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBO : B' ≤ Subgroup.normalizer (GLAPPrimeCoreOf p M : Set G) :=
    hBM.trans (normalizer_le_normalizer_glaPPrimeCoreOf p M)
  have hBX : B' ≤ Subgroup.normalizer ((⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hBM hBO
  have hX : ¬ p ∣ Nat.card ↥(⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G) := fun hd =>
    not_dvd_card_glaPPrimeCoreOf hp M (hd.trans (Subgroup.card_dvd_of_le (comm_primeCore_le_core M)))
  obtain ⟨S, hS, -, hBS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hp Nat.prime_two
    (isPGroup_of_isElemAbelian hB) hX hBX bot_le (IsPGroup.of_card (n := 0) (by simp))
    Subgroup.le_normalizer_of_normal
  obtain ⟨P, hP⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS
  refine ⟨S, hS.1, hS.2.1, ?_, hBS⟩
  have hrel : S.relIndex (⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G) = (P : Subgroup ↥(⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G)).index := by
    rw [Subgroup.relIndex, ← hP, ← Subgroup.comap_subtype]
    rw [Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
  rw [hrel]
  exact P.not_dvd_index

theorem B_not_le_centMod (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {M : Subgroup G} (hKM : K ≤ M)
    (hBM : B ≤ Subgroup.normalizer (M : Set G)) : ¬ B ≤ centModSubgroup p M := by
  intro hBc
  have hp := h.prime
  have hBD : B ≤ D := by
    rw [← centMod_inf_eq h hin]
    refine le_inf le_rfl fun b hb => ⟨B_norm_K h hb, fun k hk => ?_⟩
    have h1 : ⁅k, b⁆ ∈ GLAPPrimeCoreOf p M := (mem_centModSubgroup.1 (hBc hb)).2 k (hKM hk)
    have h2 : ⁅k, b⁆ ∈ K := by
      have e : ⁅k, b⁆ = k * (b * k⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.1 (B_norm_K h hb) k⁻¹).1 (K.inv_mem hk))
    exact inf_primeCore_le hp hKM ⟨h2, h1⟩
  have hle := Subgroup.card_le_of_le hBD
  have h4 := h.pow_four_le
  rw [h.card_D] at hle
  have : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem frattini_cover {M U : Subgroup G} (hU2 : IsPGroup 2 U) (hUX : U ≤ ⁅M, GLAPPrimeCoreOf p M⁆)
    (hUsyl : ¬ 2 ∣ U.relIndex (⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G)) :
    M = (M ⊓ Subgroup.normalizer (U : Set G)) ⊔ GLAPPrimeCoreOf p M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := ⁅M, GLAPPrimeCoreOf p M⁆ with hXdef
  have hXO : X ≤ GLAPPrimeCoreOf p M := comm_primeCore_le_core M
  have hXM : X ≤ M := hXO.trans (Subgroup.map_subtype_le _)
  have hUM : U ≤ M := hUX.trans hXM
  have hMX : M ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_commutator Subgroup.le_normalizer
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_glaPPrimeCoreOf p M))
  haveI hN0 : (X.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hMX
  have hU0N : U.subgroupOf M ≤ X.subgroupOf M := fun u hu => hUX hu
  have hP2 : IsPGroup 2 ↥((U.subgroupOf M).subgroupOf (X.subgroupOf M)) := hU2.comap_subtype.comap_subtype
  have hPidx : ¬ 2 ∣ ((U.subgroupOf M).subgroupOf (X.subgroupOf M)).index := by
    show ¬ 2 ∣ (U.subgroupOf M).relIndex (X.subgroupOf M)
    rw [Subgroup.relIndex_subgroupOf hXM]
    exact hUsyl
  let P0 : Sylow 2 ↥(X.subgroupOf M) := hP2.toSylow hPidx
  have hFr := Sylow.normalizer_sup_eq_top P0
  have hmapP : (P0 : Subgroup ↥(X.subgroupOf M)).map (X.subgroupOf M).subtype = U.subgroupOf M := by
    show ((U.subgroupOf M).subgroupOf (X.subgroupOf M)).map _ = _
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hU0N]
  rw [hmapP] at hFr
  have h1 := congrArg (Subgroup.map M.subtype) hFr
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    ← Subgroup.subgroupOf_normalizer_eq hUM, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left hXM] at h1
  refine le_antisymm ?_ (sup_le inf_le_left (Subgroup.map_subtype_le _))
  calc M = (Subgroup.normalizer (U : Set G) ⊓ M) ⊔ X := h1.symm
    _ ≤ (M ⊓ Subgroup.normalizer (U : Set G)) ⊔ GLAPPrimeCoreOf p M := sup_le_sup (inf_comm _ _).le hXO

theorem layer_covers (hp : p.Prime) {X' M C : Subgroup G} (hM : GLAPComponent p X' M) (hCM : C ≤ M)
    (hcov : M = C ⊔ GLAPPrimeCoreOf p M) : M = GLAPLayer p C ⊔ GLAPPrimeCoreOf p M := by
  obtain ⟨hOC, ⟨e⟩⟩ := cover_facts hp hCM hcov.symm
  have hq : CFSG.Open.IsQuasisimple (PQuot p C) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_pQuot_of_glaPComponent hp hM)
  obtain ⟨-, -, hbar⟩ := glaPLayer_of_isQuasisimple hq
  have hOC' : GLAPPrimeCoreOf p C ≤ GLAPPrimeCoreOf p M := by
    rw [hOC]
    exact inf_le_right
  have h1 : GLAPLayer p C ⊔ GLAPPrimeCoreOf p C = C :=
    sup_glaPPrimeCoreOf_eq_of_barX_eq_top (layer_le_self p C) hbar
  apply le_antisymm
  · calc M = C ⊔ GLAPPrimeCoreOf p M := hcov
      _ = (GLAPLayer p C ⊔ GLAPPrimeCoreOf p C) ⊔ GLAPPrimeCoreOf p M := by rw [h1]
      _ ≤ GLAPLayer p C ⊔ GLAPPrimeCoreOf p M :=
        sup_le (sup_le le_sup_left (hOC'.trans le_sup_right)) le_sup_right
  · exact sup_le ((layer_le_self p C).trans hCM) (Subgroup.map_subtype_le _)

theorem normal_eq_or_le_centMod (hp : p.Prime) {X M W : Subgroup G} (hM : GLAPComponent p X M) (hWM : W ≤ M)
    (hOW : GLAPPrimeCoreOf p M ≤ W) (hWn : M ≤ Subgroup.normalizer (W : Set G)) :
    W = M ∨ W ≤ centModSubgroup p M := by
  by_cases hWtop : W = M
  · exact Or.inl hWtop
  right
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hM
  have hWn' : (W.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWM).2 hWn
  haveI : ((W.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M))).Normal :=
    hWn'.map _ (QuotientGroup.mk'_surjective _)
  have hne : (W.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) ≠ ⊤ := by
    intro htop
    apply hWtop
    refine le_antisymm hWM (fun m hm => ?_)
    have : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨m, hm⟩ ∈
        (W.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) := htop ▸ Subgroup.mem_top _
    obtain ⟨w, hw, hwm⟩ := this
    have h1 : (w : ↥M)⁻¹ * ⟨m, hm⟩ ∈ GLAPPrimeCore p ↥M := (QuotientGroup.eq).1 hwm
    have h2 : (((w : ↥M)⁻¹ * ⟨m, hm⟩ : ↥M) : G) ∈ GLAPPrimeCoreOf p M := ⟨_, h1, rfl⟩
    have e : m = (w : G) * (((w : ↥M)⁻¹ * ⟨m, hm⟩ : ↥M) : G) := by simp
    rw [e]
    exact W.mul_mem (Subgroup.mem_subgroupOf.1 hw) (hOW h2)
  have hcen := le_center_of_normal_of_isQuasisimple hq inferInstance hne
  intro w hw
  exact mem_centModSubgroup_of_mk_mem_center (hWM hw)
    (hcen ⟨⟨w, hWM hw⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩)

theorem centMod_of_comm_centMod (hp : p.Prime) {X M B' : Subgroup G} (hM : GLAPComponent p X M)
    (hBM : B' ≤ Subgroup.normalizer (M : Set G)) (hc : (⁅M, B'⁆ : Subgroup G) ≤ centModSubgroup p M) :
    B' ≤ centModSubgroup p M := by
  have hNO := normalizer_le_normalizer_glaPPrimeCoreOf p M
  have hMO : M ≤ Subgroup.normalizer (GLAPPrimeCoreOf p M : Set G) := Subgroup.le_normalizer.trans hNO
  have hBO : B' ≤ Subgroup.normalizer (GLAPPrimeCoreOf p M : Set G) := hBM.trans hNO
  have h1 : (⁅(⁅M, B'⁆ : Subgroup G), M⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p M := by
    rw [Subgroup.commutator_le]
    intro z hz m hm
    have h2 := (mem_centModSubgroup.1 (hc hz)).2 m hm
    rw [← commutatorElement_inv m z]
    exact inv_mem h2
  have h2 : (⁅(⁅B', M⁆ : Subgroup G), M⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p M := by
    rw [Subgroup.commutator_comm B' M]
    exact h1
  have h3 := three_subgroups_mod (X := M) (Y := B') (Z := M) (N := GLAPPrimeCoreOf p M) hMO hBO hMO h1 h2
  rw [glaPComponent_perfect hM] at h3
  intro b hb
  exact ⟨hBM hb, fun l hl => h3 (Subgroup.commutator_mem_commutator hl hb)⟩

theorem closure_cover (hp : p.Prime) {X M N B' : Subgroup G} (hM : GLAPComponent p X M) (hNM : N ≤ M)
    (hcov : M = N ⊔ GLAPPrimeCoreOf p M) (hBN : B' ≤ Subgroup.normalizer (N : Set G))
    (hBM : B' ≤ Subgroup.normalizer (M : Set G)) (hBnot : ¬ B' ≤ centModSubgroup p M) :
    M = (N ⊓ closureIn B' N) ⊔ GLAPPrimeCoreOf p M := by
  have hNO := normalizer_le_normalizer_glaPPrimeCoreOf p M
  have hMO : M ≤ Subgroup.normalizer (GLAPPrimeCoreOf p M : Set G) := Subgroup.le_normalizer.trans hNO
  have hOM : GLAPPrimeCoreOf p M ≤ M := Subgroup.map_subtype_le _
  have hN₀N : N ≤ Subgroup.normalizer ((N ⊓ closureIn B' N : Subgroup G) : Set G) := fun n hn =>
    mem_normalizer_inf' (Subgroup.le_normalizer hn) (le_normalizer_closureIn_self B' N hn)
  have hWM : (N ⊓ closureIn B' N) ⊔ GLAPPrimeCoreOf p M ≤ M := sup_le (inf_le_left.trans hNM) hOM
  have hMW : M ≤ Subgroup.normalizer (((N ⊓ closureIn B' N) ⊔ GLAPPrimeCoreOf p M : Subgroup G) : Set G) := by
    intro m hm
    have hm' : m ∈ N ⊔ GLAPPrimeCoreOf p M := hcov ▸ hm
    have hle : N ⊔ GLAPPrimeCoreOf p M ≤ Subgroup.normalizer
        (((N ⊓ closureIn B' N) ⊔ GLAPPrimeCoreOf p M : Subgroup G) : Set G) :=
      sup_le (fun n hn => mem_normalizer_sup' (hN₀N hn) (hMO (hNM hn)))
        (fun o ho => Subgroup.le_normalizer (le_sup_right (a := N ⊓ closureIn B' N) ho))
    exact hle hm'
  rcases normal_eq_or_le_centMod hp hM hWM le_sup_right hMW with h | h
  · exact h.symm
  · exfalso
    apply hBnot
    refine centMod_of_comm_centMod hp hM hBM ?_
    have hcN : ∀ n ∈ N, ∀ b ∈ B', ⁅n, b⁆ ∈ centModSubgroup p M := by
      intro n hn b hb
      refine h (le_sup_left (a := N ⊓ closureIn B' N) ⟨?_, ?_⟩)
      · have e : ⁅n, b⁆ = n * (b * n⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem hn ((Subgroup.mem_normalizer_iff.1 (hBN hb) n⁻¹).1 (N.inv_mem hn))
      · have h1 : n * b * n⁻¹ ∈ closureIn B' N := by
          have : n * b * n⁻¹ ∈ GLBConj n⁻¹ B' := by
            rw [mem_gLBConj]
            have e : n⁻¹ * (n * b * n⁻¹) * n⁻¹⁻¹ = b := by group
            rw [e]
            exact hb
          rw [closureIn_eq_iSup_gLBConj]
          exact (le_biSup (fun h => GLBConj h B') (N.inv_mem hn)) this
        have h2 : b⁻¹ ∈ closureIn B' N := le_closureIn_self B' N (B'.inv_mem hb)
        exact mul_mem h1 h2
    rw [Subgroup.commutator_le]
    intro m hm b hb
    have hm' : m ∈ N ⊔ GLAPPrimeCoreOf p M := hcov ▸ hm
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right N _ (fun n hn => hMO (hNM hn))] at hm'
    obtain ⟨n, hn, o, ho, rfl⟩ := Set.mem_mul.mp hm'
    have hbO : b ∈ Subgroup.normalizer (GLAPPrimeCoreOf p M : Set G) := hBM.trans hNO |>.trans le_rfl <| hb
    have e : ⁅n * o, b⁆ = n * ⁅o, b⁆ * n⁻¹ * ⁅n, b⁆ := by simp only [commutatorElement_def]; group
    rw [e]
    have hob : ⁅o, b⁆ ∈ GLAPPrimeCoreOf p M := by
      have e2 : ⁅o, b⁆ = o * (b * o⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
      rw [e2]
      exact mul_mem ho ((Subgroup.mem_normalizer_iff.1 hbO o⁻¹).1 (inv_mem ho))
    exact mul_mem (S3.conj_mem_centModSubgroup (Subgroup.le_normalizer (hNM hn))
      (L62.glaPPrimeCoreOf_le_centModSubgroup p M hob)) (hcN n hn b hb)

theorem exists_cover_le_closure (hp : p.Prime) {Y M B' U : Subgroup G} (hM : GLAPComponent p Y M)
    (hcov : M = (M ⊓ Subgroup.normalizer (U : Set G)) ⊔ GLAPPrimeCoreOf p M)
    (hBU : B' ≤ Subgroup.normalizer (U : Set G)) (hBM : B' ≤ Subgroup.normalizer (M : Set G))
    (hBnot : ¬ B' ≤ centModSubgroup p M) :
    ∃ N : Subgroup G, N ≤ M ⊓ Subgroup.normalizer (U : Set G) ∧ M = N ⊔ GLAPPrimeCoreOf p M ∧ N ≤ closureIn B' N := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hNO := normalizer_le_normalizer_glaPPrimeCoreOf p M
  have hMO : M ≤ Subgroup.normalizer (GLAPPrimeCoreOf p M : Set G) := Subgroup.le_normalizer.trans hNO
  have hBNU : B' ≤ Subgroup.normalizer ((Subgroup.normalizer (U : Set G) : Subgroup G) : Set G) := fun b hb => by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨fun ht => mul_mem (mul_mem (hBU hb) ht) (inv_mem (hBU hb)), fun ht => ?_⟩
    have h1 := mul_mem (mul_mem (hBU (inv_mem hb)) ht) (inv_mem (hBU (inv_mem hb)))
    have e : b⁻¹ * (b * t * b⁻¹) * b⁻¹⁻¹ = t := by group
    rwa [e] at h1
  set H : Subgroup G := M ⊓ Subgroup.normalizer (U : Set G) with hHdef
  have hHM : H ≤ M := inf_le_left
  have hBH : B' ≤ Subgroup.normalizer (H : Set G) := fun b hb => mem_normalizer_inf' (hBM hb) (hBNU hb)
  have hNM : GLAPLayer p H ≤ M := (layer_le_self p H).trans hHM
  have hNcov : M = GLAPLayer p H ⊔ GLAPPrimeCoreOf p M := layer_covers hp hM hHM hcov
  have hBN : B' ≤ Subgroup.normalizer (GLAPLayer p H : Set G) := fun b hb => mem_normalizer_glaPLayer (hBH hb)
  have h1 := closure_cover hp hM hNM hNcov hBN hBM hBnot
  have hNp := pPrimePerfect_glaPLayer p H
  have hN₀N : GLAPLayer p H ≤ Subgroup.normalizer ((GLAPLayer p H ⊓ closureIn B' (GLAPLayer p H) : Subgroup G) : Set G) :=
    fun n hn => mem_normalizer_inf' (Subgroup.le_normalizer hn) (le_normalizer_closureIn_self B' _ hn)
  have hnorm : ((GLAPLayer p H ⊓ closureIn B' (GLAPLayer p H)).subgroupOf (GLAPLayer p H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hN₀N
  have hidx : Nat.Coprime ((GLAPLayer p H ⊓ closureIn B' (GLAPLayer p H)).relIndex (GLAPLayer p H)) p :=
    coprime_relIndex_of_normal (Θ := GLAPPrimeCoreOf p M)
      (inf_le_left.trans (hNM.trans hMO))
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp M)).symm inf_le_left
      (by rw [← h1]; exact hNM) hnorm
  have heq := hNp _ inf_le_left hnorm hidx
  exact ⟨GLAPLayer p H, layer_le_self p H, hNcov, heq.symm.le.trans inf_le_right⟩

theorem closureIn_le_cs {B' N U : Subgroup G} (hN : N ≤ Subgroup.normalizer (U : Set G))
    (hB : B' ≤ Subgroup.centralizer (U : Set G)) : closureIn B' N ≤ Subgroup.centralizer (U : Set G) := by
  rw [closureIn_eq_iSup_gLBConj]
  refine iSup₂_le fun n hn z hz => ?_
  rw [mem_gLBConj] at hz
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : n * u * n⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hN hn) u).1 hu
  have h1 := Subgroup.mem_centralizer_iff.1 (hB hz) _ hu'
  have h2 : n * (u * z) * n⁻¹ = n * (z * u) * n⁻¹ := by
    calc n * (u * z) * n⁻¹ = (n * u * n⁻¹) * (n * z * n⁻¹) := by group
      _ = (n * z * n⁻¹) * (n * u * n⁻¹) := h1
      _ = n * (z * u) * n⁻¹ := by group
  simpa using h2

theorem cover_of_centralizes (hp : p.Prime) (hp2 : p ≠ 2) {d : G} {M B' U : Subgroup G}
    (hM : GLAPComponent p (Subgroup.centralizer ({d} : Set G)) M) (hBM : B' ≤ Subgroup.normalizer (M : Set G))
    (hB : IsElemAbelian p B') (hBnot : ¬ B' ≤ centModSubgroup p M) (hU2 : IsPGroup 2 U)
    (hUX : U ≤ ⁅M, GLAPPrimeCoreOf p M⁆) (hUsyl : ¬ 2 ∣ U.relIndex (⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G))
    (hBU : B' ≤ Subgroup.centralizer (U : Set G)) :
    M = (M ⊓ Subgroup.centralizer (U : Set G)) ⊔ GLAPPrimeCoreOf p M := by
  have hBU' : B' ≤ Subgroup.normalizer (U : Set G) := fun b hb => Subgroup.centralizer_le_normalizer _ (hBU hb)
  obtain ⟨N, hNle, hNcov, hNcl⟩ := exists_cover_le_closure hp hM (frattini_cover hU2 hUX hUsyl) hBU' hBM hBnot
  have hNcs : N ≤ Subgroup.centralizer (U : Set G) :=
    hNcl.trans (closureIn_le_cs (fun n hn => (hNle hn).2) hBU)
  have hOM : GLAPPrimeCoreOf p M ≤ M := calc
    GLAPPrimeCoreOf p M ≤ N ⊔ GLAPPrimeCoreOf p M := le_sup_right
    _ = M := hNcov.symm
  refine le_antisymm ?_ (sup_le inf_le_left hOM)
  calc M = N ⊔ GLAPPrimeCoreOf p M := hNcov
    _ ≤ (M ⊓ Subgroup.centralizer (U : Set G)) ⊔ GLAPPrimeCoreOf p M :=
      sup_le_sup_right (le_inf (hNle.trans inf_le_left) hNcs) _

theorem sylow_trivial (h1810 : Input18_10) (hp : p.Prime) {d : G} {M U : Subgroup G} (hKM : CFSG.Open.IsKGroup ↥M)
    (hM : GLAPComponent p (Subgroup.centralizer ({d} : Set G)) M) (hU2 : IsPGroup 2 U)
    (hUX : U ≤ ⁅M, GLAPPrimeCoreOf p M⁆) (hUsyl : ¬ 2 ∣ U.relIndex (⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G))
    (hcov : M = (M ⊓ Subgroup.centralizer (U : Set G)) ⊔ GLAPPrimeCoreOf p M) : U = ⊥ := by
  by_contra hU
  haveI : Fact p.Prime := ⟨hp⟩
  have hMM : GLAPComponent p M M := glaPComponent_of_le hp hM le_rfl hM.1
  have h2 : 2 ∣ Nat.card ↥(⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hU2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hU (Subgroup.card_eq_one.1 (by rw [hn, pow_zero]))
    have := Subgroup.card_dvd_of_le hUX
    rw [hn] at this
    exact (dvd_pow_self 2 hn0).trans this
  have hC := h1810 G M hKM p hp hMM 2 Nat.prime_two U h2 hUX hU2 hUsyl
  have hOle : GLAPPrimeCoreOf p M ≤ oPrimeP p M := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n, ?_, rfl⟩
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥M) n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    show QuotientGroup.mk' (GLAPPrimeCore p ↥M) n ∈ CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M)
    rw [h1]
    exact one_mem _
  have hMle : M ≤ oPrimeP p M := by
    calc M = (M ⊓ Subgroup.centralizer (U : Set G)) ⊔ GLAPPrimeCoreOf p M := hcov
      _ ≤ oPrimeP p M := sup_le hC hOle
  have hPG : IsPGroup p (PQuot p M) := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H n =>
      obtain ⟨n', hn', hnn'⟩ := hMle n.2
      have hnn : n' = n := Subtype.ext hnn'
      subst hnn
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := PQuot p M)) ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥M) n', hn'⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  exact not_isPGroup_of_isQuasisimple (isQuasisimple_pQuot_of_glaPComponent hp hM) hPG

theorem oddCore_of_cover (h : Cfg12 G m p B x L D K) (hin : Inputs121 G p) (h1810 : Input18_10) {d : G} (hd : d ∈ D)
    (hd1 : d ≠ 1) {M : Subgroup G} (hM : GLAPComponent p (Subgroup.centralizer ({d} : Set G)) M) (hKM : K ≤ M)
    (hBM : B ≤ Subgroup.normalizer (M : Set G)) (hcov : M = K ⊔ GLAPPrimeCoreOf p M) :
    Odd (Nat.card ↥(⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G)) := by
  have hcom := hin.common
  rcases lemma121 h hin with ⟨hU, hp3, hd2, hinner, hL⟩ | ⟨hns, hd5, E, hE, hDE, hEL, hEK⟩
  ·
    by_contra hev
    have h2 : 2 ∣ Nat.card ↥(⁅M, GLAPPrimeCoreOf p M⁆ : Subgroup G) := by
      rw [Nat.not_odd_iff_even] at hev
      exact even_iff_two_dvd.1 hev
    obtain ⟨U, hUX, hU2, hUsyl, hUB⟩ := exists_invariant_sylow_comm h.prime h.odd hM h.tri.bmax.1 hBM
    have hUne : U ≠ ⊥ := by
      rintro rfl
      apply hUsyl
      rw [Subgroup.relIndex_bot_left]
      exact h2
    have hUO : U ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G)) :=
      hUX.trans ((comm_primeCore_le_core M).trans
        (glaPPrimeCoreOf_le_of_isSubnormal h.prime hM.2.1))
    have hcomm : (⁅U, B⁆ : Subgroup G) = ⊥ := by
      subst hp3
      exact h.ctx.ctx.stage4.2.2 hd2.le B d U h.tri.bmax (h.DB hd) hd1 hUO hU2 hUB
    have hBU : B ≤ Subgroup.centralizer (U : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hcomm
    have hBnot := B_not_le_centMod h hcom hKM hBM
    have hcen := cover_of_centralizes h.prime h.odd hM hBM h.tri.bmax.1 hBnot hU2 hUX hUsyl hBU
    exact hUne (sylow_trivial h1810 h.prime (isKGroup_le_cx h hd1 hM.1) hM hU2 hUX hUsyl hcen)
  ·
    have hG : IsGStar p B M := by
      refine ⟨E, hE.1, hE.2.1, hE.2.2, ?_⟩
      rw [closureIn_eq_self hBM]
      exact layer_up h hcom hE hDE hKM hEK
    have h4 := h.ctx.ctx.stage4.2.1 B d M h.tri.bmax (h.DB hd) hd1 hM hG
    rw [closureIn_eq_self hBM] at h4
    exact Odd.of_dvd_nat h4 (Subgroup.card_dvd_of_le
      (Subgroup.commutator_mono le_rfl (glaPPrimeCoreOf_le_of_isSubnormal h.prime hM.2.1)))

end S12

end CFSG.LocalAnalysis.GLTheoremA
