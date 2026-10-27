module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4Comp
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4aFit
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4a
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S3B
import CFSG.GH74.AS16.Standard
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Closed
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt18
public import CFSG.GH74.GLS.Stage2.Local.Basic
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Basic
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs
import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

namespace P2S4

section Helpers

variable {G : Type} [Group G]

theorem commutator_eq_of_not_le_centralizer {J Z : Subgroup G} (hq : IsQuasisimple ↥J)
    (hZ : Z ≤ normalizer (J : Set G)) (hnc : ¬ Z ≤ centralizer (J : Set G)) : ⁅J, Z⁆ = J := by
  have hperf : Group.IsPerfect ↥J := hq.1
  set L := ⁅J, Z⁆ with hL
  have hLJ : L ≤ J := by
    rw [hL, Subgroup.commutator_le]
    intro a ha b hb
    have hbN : b ∈ normalizer (J : Set G) := hZ hb
    have h1 := (mem_normalizer_iff.mp hbN a⁻¹).mp (J.inv_mem ha)
    rw [commutatorElement_def]
    simpa [mul_assoc] using J.mul_mem ha h1
  have hnorm : ∀ g ∈ J, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg
    have h1 : L ≤ L.comap (MulAut.conj g).toMonoidHom := by
      rw [hL, Subgroup.commutator_le]
      intro a ha b hb
      show g * ⁅a, b⁆ * g⁻¹ ∈ L
      have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a, b⁆ * ⁅g, b⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact L.mul_mem (Subgroup.commutator_mem_commutator (J.mul_mem hg ha) hb)
        (L.inv_mem (Subgroup.commutator_mem_commutator hg hb))
    intro l hl
    exact h1 hl
  have hLn : (L.subgroupOf J).Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ L := hn
    exact hnorm (g : G) g.2 (n : G) hn'⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hLn with htop | hcen
  · exact le_antisymm hLJ (Subgroup.subgroupOf_eq_top.mp htop)
  · exfalso
    apply hnc
    have := hperf
    intro g hg
    have hgJ : g ∈ centralizer (J : Set G) :=
      P2S3.mem_centralizer_of_comm_central (hZ hg) fun j hj k hk => by
        have hmem : (⟨g * j * g⁻¹ * j⁻¹, by
            have h1 : g * j * g⁻¹ ∈ J := (mem_normalizer_iff.mp (hZ hg) j).mp hj
            exact J.mul_mem h1 (J.inv_mem hj)⟩ : ↥J) ∈ L.subgroupOf J := by
          have h1 : ⁅j, g⁆ ∈ L := Subgroup.commutator_mem_commutator hj hg
          have h2 : ⁅g, j⁆ = ⁅j, g⁆⁻¹ := (commutatorElement_inv j g).symm
          show g * j * g⁻¹ * j⁻¹ ∈ L
          have h3 : g * j * g⁻¹ * j⁻¹ = ⁅g, j⁆ := by simp [commutatorElement_def]
          rw [h3, h2]
          exact L.inv_mem h1
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcen hmem) ⟨k, hk⟩)
    exact hgJ

omit [Group G] in
theorem eq_of_subgroupOf_eq {G : Type} [Group G] {H K₁ K₂ : Subgroup G} (h₁ : K₁ ≤ H)
    (h₂ : K₂ ≤ H) (h : K₁.subgroupOf H = K₂.subgroupOf H) : K₁ = K₂ := by
  have := Subgroup.subgroupOf_inj.mp h
  rwa [inf_of_le_left h₁, inf_of_le_left h₂] at this

end Helpers

end P2S4

theorem lemma18_3a_of_182 (h182 : Lemma18_2) (h171 : Prop17_1) (hL31 : Lemma31Narrow) :
    Lemma18_3a := by
  intro G _ _ z k S M p E t hctx X hXv hXM hXtop J hJ
  have hS2 : Stage2Ctx G z k S := hctx.base.ctx.ctx
  have hMz : M = centralizer ({z} : Set G) := (h171 G z k S M hctx.base.ctx hctx.base.fail).1
  have hz2' : orderOf z = 2 := hS2.orderOf_z
  have hz2 : z * z = 1 := by
    have : z ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq hz2')
    simpa [pow_two] using this
  have hp : p.Prime := hctx.prime
  have hzV : z ∈ Vof M E := P2S4a.z_mem_Vof hMz hz2' hctx.E_le
  have hzX : z ∈ normalizer (X : Set G) := hXv z hzV
  have hMc : IsCoatom M := hctx.base.ctx.mem.1
  have hsimple : IsSimpleGroup G := hctx.base.ctx.ctx.std.kps.1
  have hVle : Vof M E ≤ M := inf_le_left.trans (Fm_le M)
  have hVX : Vof M E ≤ normalizer (X : Set G) := fun v hv => hXv v hv
  have hPV : ∀ v ∈ pPrimeCoreOf 2 (Vof M E), v ∈ Vof M E := fun v hv =>
    (Subgroup.map_subtype_le _) hv
  have hJq : IsQuasisimple ↥J := P2S3.quasisimple_of_isCompIn hJ
  have hnebot : ∀ D : Subgroup G, IsQuasisimple ↥D → D ≠ ⊥ := fun D hD =>
    (Subgroup.nontrivial_iff_ne_bot D).mp (CFSG.LocalCores.isQuasisimple_nontrivial hD)
  set H : Subgroup G := X ⊔ Vof M E ⊔ zpowers z with hH
  have hXH : X ≤ H := le_sup_left.trans le_sup_left
  have hVH : Vof M E ≤ H := le_sup_right.trans le_sup_left
  have hzH : z ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hHN : H ≤ normalizer (X : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hVX) (Subgroup.zpowers_le.mpr hzX)
  have hXbot : X ≠ ⊥ := fun h => hnebot J hJq (le_bot_iff.mp (h ▸ hJ.1))
  have hHtop : H ≠ ⊤ := by
    intro htop
    have hn : X.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact top_le_iff.mp (htop ▸ hHN)
    rcases hsimple.eq_bot_or_eq_top_of_normal X with h | h
    · exact hXbot h
    · exact hXtop h
  have hcomp : ∀ K : Subgroup G, IsCompIn X K → IsCompIn H K := fun K hK =>
    P2S4.isCompIn_of_normal hXH hHN hK
  have hno3 : ∀ K₁ K₂ K₃ : Subgroup ↥H, IsComponent K₁ → IsComponent K₂ → IsComponent K₃ →
      K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃ := fun K₁ K₂ K₃ h₁ h₂ h₃ =>
    P2S3.comps_le_two hL31 hS2 hHtop hzH h₁ h₂ h₃
  have hJH : IsCompIn H J := hcomp J hJ
  have hncard : Set.ncard {K : Subgroup G | IsCompIn X K} ≤ 2 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).mp hlt
    have ha' := hcomp a ha
    have hb' := hcomp b hb
    have hc' := hcomp c hc
    rcases hno3 _ _ _ ha'.2 hb'.2 hc'.2 with h | h | h
    · exact hab (P2S4.eq_of_subgroupOf_eq ha'.1 hb'.1 h)
    · exact hac (P2S4.eq_of_subgroupOf_eq ha'.1 hc'.1 h)
    · exact hbc (P2S4.eq_of_subgroupOf_eq hb'.1 hc'.1 h)
  have hoddN : ∀ v ∈ H, Odd (orderOf v) → ∀ J' : Subgroup G, IsCompIn H J' →
      v ∈ normalizer (J' : Set G) := fun v hv hodd J' hJ' =>
    P2S3.mem_normalizer_of_odd hno3 hJ' hv hodd
  have hzN : ∀ J' : Subgroup G, IsCompIn X J' → z ∈ normalizer (J' : Set G) := by
    intro J' hJ'
    by_contra hzn
    have hJ'H := hcomp J' hJ'
    have hne : J' ≠ J'.map (MulAut.conj z).toMonoidHom := fun h =>
      hzn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
    have hJ'c := P2S3.isCompIn_map_conj_of_mem hJ'H hzH
    rcases AS16.isCompIn_commute hJ'H hJ'c with h | h
    · exact hne h
    · have hcomm : ∀ a ∈ J', ∀ b ∈ J'.map (MulAut.conj z).toMonoidHom, a * b = b * a := by
        intro a ha b hb
        have h1 : ⁅a, b⁆ ∈ ⁅J', J'.map (MulAut.conj z).toMonoidHom⁆ :=
          Subgroup.commutator_mem_commutator ha hb
        rw [h, Subgroup.mem_bot, commutatorElement_def] at h1
        calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
          _ = b * a := by rw [h1, one_mul]
      have hq' : IsQuasisimple ↥J' := P2S3.quasisimple_of_isCompIn hJ'H
      have hDq := P2S4.isQuasisimple_range_diagHom (z := z) (hcomm := hcomm) hq'
      have hDM : (P2S4.diagHom z J' hcomm).range ≤ M := by
        rintro _ ⟨u, rfl⟩
        rw [hMz]
        exact P2S4.diagHom_mem_centralizer hz2 u
      have hDv : ∀ v ∈ pPrimeCoreOf 2 (Vof M E),
          v ∈ normalizer (((P2S4.diagHom z J' hcomm).range : Subgroup G) : Set G) := by
        intro v hv
        have hvV := hPV v hv
        have hvz : v * z = z * v :=
          Subgroup.mem_centralizer_singleton_iff.1 (hMz ▸ hVle hvV : v ∈ centralizer ({z} : Set G))
        have hvN := hoddN v (hVH hvV) (P2S4.odd_orderOf_of_mem_pPrimeCoreOf hv) J' hJ'H
        refine P2S4.mem_normalizer_of_forall_conj fun d hd => ?_
        obtain ⟨u, rfl⟩ := hd
        have hu : v * (u : G) * v⁻¹ ∈ J' := (mem_normalizer_iff.mp hvN u).mp u.2
        rw [P2S4.diagHom_conj hvz u hu]
        exact ⟨_, rfl⟩
      obtain ⟨-, hzD⟩ := h182 G z k S M p E t hctx _ hDM (hnebot _ hDq) hDv
        (P2S4.Em_eq_of_isQuasisimple hDq)
      exact hzn (P2S4.mem_normalizer_of_mem_range_diagHom hzD)
  have hJM : ∀ J' : Subgroup G, IsCompIn X J' → ¬ J' ≤ M := by
    intro J' hJ' hle
    have hJ'H := hcomp J' hJ'
    have hq' := P2S3.quasisimple_of_isCompIn hJ'H
    have hinv : ∀ v ∈ pPrimeCoreOf 2 (Vof M E), v ∈ normalizer (J' : Set G) := fun v hv =>
      hoddN v (hVH (hPV v hv)) (P2S4.odd_orderOf_of_mem_pPrimeCoreOf hv) J' hJ'H
    obtain ⟨-, hzJ'⟩ := h182 G z k S M p E t hctx J' hle (hnebot J' hq') hinv
      (P2S4.Em_eq_of_isQuasisimple hq')
    have hall : ∀ K : Subgroup G, IsCompIn X K → K ≤ M := by
      intro K hK
      rcases AS16.isCompIn_commute hK hJ' with h | h
      · rw [h]
        exact hle
      · intro y hy
        rw [hMz, Subgroup.mem_centralizer_singleton_iff]
        have h1 : ⁅y, z⁆ ∈ ⁅K, J'⁆ := Subgroup.commutator_mem_commutator hy hzJ'
        rw [h, Subgroup.mem_bot, commutatorElement_def] at h1
        calc y * z = y * z * y⁻¹ * z⁻¹ * (z * y) := by group
          _ = z * y := by rw [h1, one_mul]
    have hEM : Em X ≤ M := P2S4.Em_le_of_comps_le hall
    have hE0 : Em X ≠ ⊥ := fun h =>
      hnebot J' hq' (le_bot_iff.mp (h ▸ P2S4.le_Em_of_isCompIn hJ'))
    have hEinv : ∀ v ∈ pPrimeCoreOf 2 (Vof M E), v ∈ normalizer ((Em X : Subgroup G) : Set G) :=
      fun v hv => P2S4a.mem_normalizer_Em (hXv v (hPV v hv))
    obtain ⟨hrk, hzE⟩ := h182 G z k S M p E t hctx (Em X) hEM hE0 hEinv (P2S4.Em_Em X)
    apply hXM
    intro x hx
    rw [hMz, Subgroup.mem_centralizer_singleton_iff]
    by_contra hxz
    have hxN : x ∈ normalizer ((Em X : Subgroup G) : Set G) :=
      P2S4a.mem_normalizer_Em (Subgroup.le_normalizer hx)
    have hw : x * z * x⁻¹ ∈ Em X := (mem_normalizer_iff.mp hxN z).mp hzE
    have hwz : x * z * x⁻¹ ≠ z := fun h => hxz (by
      calc x * z = (x * z * x⁻¹) * x := by group
        _ = z * x := by rw [h])
    have hcomm : z * (x * z * x⁻¹) = (x * z * x⁻¹) * z := by
      have : x * z * x⁻¹ ∈ centralizer ({z} : Set G) := hMz ▸ hEM hw
      exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
    have hord : orderOf (x * z * x⁻¹) = 2 := by
      have h1 : orderOf ((MulAut.conj x).toMonoidHom z) = orderOf z :=
        orderOf_injective _ (MulAut.conj x).injective z
      rw [hz2'] at h1
      simpa [MulAut.conj_apply] using h1
    have hrk2 := P2S4.two_le_pRank_of_klein hzE hw hz2' hord (Ne.symm hwz) hcomm
    omega
  have hJz : ⁅J, zpowers z⁆ = J := P2S3.commutator_eq hMz hJH (hzN J hJ) (hJM J hJ)
  set Z : Subgroup G := omega1Z p (Op p M) with hZ
  have hZP : Z ≤ Op p M := P2S4.omega1Z_le p _
  have hZV : Z ≤ Vof M E := by
    intro x hx
    refine ⟨Op_le_Fm p hp M (hZP hx), Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
    exact (hx.2.1 e (hctx.E_le he)).symm
  have hZodd : ∀ x ∈ Z, Odd (orderOf x) := by
    intro x hx
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx.2.2
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · rw [h]
      exact odd_one
    · rw [h]
      exact hp.odd_of_ne_two hctx.odd
  have hZN : Z ≤ normalizer (J : Set G) := fun x hx =>
    hoddN x (hVH (hZV hx)) (hZodd x hx) J hJH
  have hMZ : M ≤ normalizer (Z : Set G) := fun m hm =>
    P2S4.mem_normalizer_of_forall_conj fun x hx =>
      P2S4.omega1Z_conj_mem (le_normalizer_Op p M hm) hx
  have ht1 : t ≠ 1 := by
    intro h
    have := hctx.t_ord
    rw [h, orderOf_one] at this
    exact hp.one_lt.ne this
  have hZbot : Z ≠ ⊥ := P2S4.omega1Z_ne_bot hp (isPGroup_Op p hp M) hctx.t_mem ht1
  have hZtop : Z ≠ ⊤ := by
    intro h
    apply hMc.1
    have : (⊤ : Subgroup G) ≤ M := h ▸ (hZP.trans (Op_le p M))
    exact top_le_iff.mp this
  have hNZ : normalizer (Z : Set G) = M :=
    P2S4.normalizer_eq_of_coatom hsimple hMc hZbot hZtop hMZ
  have hZnc : ¬ Z ≤ centralizer (J : Set G) := by
    intro hZc
    apply hJM J hJ
    intro j hj
    have hjc : j ∈ centralizer (Z : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hZc hx) j hj).symm
    rw [← hNZ]
    exact Subgroup.centralizer_le_normalizer _ hjc
  exact ⟨hncard, hJz, P2S4.commutator_eq_of_not_le_centralizer hJq hZN hZnc⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
