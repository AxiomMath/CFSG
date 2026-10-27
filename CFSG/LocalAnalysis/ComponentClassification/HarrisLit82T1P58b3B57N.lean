module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3B57

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open scoped MatrixGroups

namespace P58b3

@[expose] def OddAutInnerFix (X : Type) [Group X] (c : X) : Prop :=
  ∀ α : MulAut X, α c = c → ∀ k : ℕ, Odd k → α ^ k ∈ (MulAut.conj : X →* MulAut X).range →
    α ∈ (MulAut.conj : X →* MulAut X).range

theorem OddAutInner.fix {X : Type} [Group X] (h : OddAutInner X) (c : X) :
    OddAutInnerFix X c :=
  fun α _ k hk hα => h α k hk hα

theorem OddAutInnerFix.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {c : X}
    (h : OddAutInnerFix Y (e c)) : OddAutInnerFix X c := by
  intro α hαc k hk hα
  obtain ⟨x, hx⟩ := hα
  have hβc : MulAut.congr e α (e c) = e c := by
    change e (α (e.symm (e c))) = e c
    rw [MulEquiv.symm_apply_apply, hαc]
  have hβ : (MulAut.congr e α) ^ k ∈ (MulAut.conj : Y →* MulAut Y).range :=
    ⟨e x, by rw [← map_pow, ← hx, OuterAutomorphisms.congr_conj]⟩
  obtain ⟨y, hy⟩ := h _ hβc k hk hβ
  refine ⟨e.symm y, ?_⟩
  apply (MulAut.congr e).injective
  rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, hy]

variable {G : Type} [Group G] [Finite G]

theorem le_sup_of_normalizer_le_centralizer {W H D : Subgroup G} (hWH : W ≤ H)
    (hW : (W.subgroupOf H).Normal)
    (hnc : ∀ S : Sylow 2 ↥W, normalizer (S : Set ↥W) ≤ centralizer (S : Set ↥W))
    (hD : ∀ x ∈ W, ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ D) :
    W ≤ (pPrimeCore 2 ↥H).map H.subtype ⊔ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOW := F3L57.map_pPrimeCore_le_of_normal hWH hW
  let S : Sylow 2 ↥W := Classical.choice Sylow.nonempty
  have hc := MonoidHom.ker_transferSylow_isComplement' S (hnc S)
  set N := (MonoidHom.transferSylow S (hnc S)).ker with hNdef
  have hNodd : ¬ 2 ∣ Nat.card N := MonoidHom.not_dvd_card_ker_transferSylow S _
  have hNO : N ≤ pPrimeCore 2 ↥W :=
    F3L57.le_pPrimeCore_of_normal (MonoidHom.normal_ker _)
      (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hNodd))
  have htop : N ⊔ (S : Subgroup ↥W) = ⊤ := hc.sup_eq_top
  intro w hw
  have hw' : (⟨w, hw⟩ : ↥W) ∈ N ⊔ (S : Subgroup ↥W) := htop ▸ mem_top _
  have hmap : (N ⊔ (S : Subgroup ↥W)).map W.subtype ≤ (pPrimeCore 2 ↥H).map H.subtype ⊔ D := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ((map_mono hNO).trans hOW) ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨k, hk⟩ := S.2 ⟨s, hs⟩
    refine hD _ s.2 k ?_
    have hk' : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    simpa using congrArg Subtype.val hk'
  exact hmap ⟨⟨w, hw⟩, hw', rfl⟩

theorem le_sup_pPrimeCore_of_autFix {M : Subgroup G} [hMn : M.Normal]
    (hM2 : ∀ g : G, ∀ k : ℕ, g ^ 2 ^ k = 1 → g ∈ M) {c₀ : G} (hc₀ : c₀ ∈ M) {z : G}
    (hcen : centralizer ({z} : Set G) ≤ centralizer {c₀})
    (ha : OddAutInnerFix (↥M ⧸ pPrimeCore 2 ↥M) (QuotientGroup.mk ⟨c₀, hc₀⟩))
    (hz : orderOf z = 2) (hzX : z ∈ M) :
    centralizer ({z} : Set G) ≤ (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map
      (centralizer {z}).subtype ⊔ M ⊓ centralizer {z} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({z} : Set G) with hHdef
  set D := M ⊓ H with hDdef
  set ψ : G →* MulAut (↥M ⧸ pPrimeCore 2 ↥M) :=
    UnbalancingLocal.conjQuotAction M (pPrimeCore 2 ↥M) with hψ
  set z' : ↥M := ⟨z, hzX⟩ with hz'
  have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact hz
  have hOMo : Odd (Nat.card (pPrimeCore 2 ↥M)) := F3L57.odd_card_pPrimeCore ↥M
  have hstep : ∀ h ∈ H, ∃ d ∈ D, d⁻¹ * h ∈ ψ.ker := by
    intro h hh
    obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
    have hhm : h ^ m ∈ M := hM2 _ a (by
      rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one])
    have hinner : ψ h ^ m ∈ (MulAut.conj : (↥M ⧸ pPrimeCore 2 ↥M) →* MulAut _).range := by
      rw [← map_pow]
      exact ⟨_, (UnbalancingLocal.conjQuotAction_coe (Z := pPrimeCore 2 ↥M)
        (⟨h ^ m, hhm⟩ : ↥M)).symm⟩
    have hhc : h * c₀ * h⁻¹ = c₀ := by
      have := mem_centralizer_singleton_iff.mp (hcen hh)
      rw [this, mul_inv_cancel_right]
    have hψc : ψ h (QuotientGroup.mk ⟨c₀, hc₀⟩) = QuotientGroup.mk ⟨c₀, hc₀⟩ := by
      rw [hψ, UnbalancingLocal.conjQuotAction_mk' h ⟨c₀, hc₀⟩ (by
        show h * c₀ * h⁻¹ ∈ M
        rw [hhc]
        exact hc₀)]
      exact congrArg _ (Subtype.ext hhc)
    obtain ⟨x, hx⟩ := ha _ hψc m hm hinner
    obtain ⟨m₀, rfl⟩ := QuotientGroup.mk_surjective x
    have hhz : h * z * h⁻¹ = z := by
      rw [mem_centralizer_singleton_iff] at hh
      rw [hh, mul_inv_cancel_right]
    have hfix : MulAut.conj (m₀ : ↥M ⧸ pPrimeCore 2 ↥M) (z' : ↥M ⧸ pPrimeCore 2 ↥M) =
        (z' : ↥M ⧸ pPrimeCore 2 ↥M) := by
      rw [hx, hψ, UnbalancingLocal.conjQuotAction_mk' h z' (by
        show h * z * h⁻¹ ∈ M
        rw [hhz]
        exact hzX)]
      exact congrArg _ (Subtype.ext hhz)
    have hcen' : QuotientGroup.mk' (pPrimeCore 2 ↥M) m₀ ∈
        centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥M) z'} : Set (↥M ⧸ pPrimeCore 2 ↥M)) := by
      rw [mem_centralizer_singleton_iff]
      rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hfix
      exact hfix
    rw [← FooteLit.map_centralizer_mk'_of_odd hOMo hz'2] at hcen'
    obtain ⟨d', hd', hd'm⟩ := hcen'
    have hdH : (d' : G) ∈ H := by
      rw [hHdef, mem_centralizer_singleton_iff]
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hd'
      exact congrArg Subtype.val hd'
    refine ⟨d', ⟨d'.2, hdH⟩, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hx, hψ,
      UnbalancingLocal.conjQuotAction_coe (Z := pPrimeCore 2 ↥M) d']
    have hdm : (d' : ↥M ⧸ pPrimeCore 2 ↥M) = (m₀ : ↥M ⧸ pPrimeCore 2 ↥M) := hd'm
    rw [hdm, inv_mul_cancel]
  set W := ψ.ker ⊓ H with hWdef
  have hWH : W ≤ H := inf_le_right
  have hWn : (W.subgroupOf H).Normal := by
    rw [hWdef, inf_subgroupOf_right]
    infer_instance
  have hnc : ∀ S : Sylow 2 ↥W, normalizer (S : Set ↥W) ≤ centralizer (S : Set ↥W) := by
    intro S w hw
    rw [mem_centralizer_iff]
    intro s hs
    have hs' : w * s * w⁻¹ ∈ (S : Subgroup ↥W) := (mem_normalizer_iff.mp hw s).mp hs
    have h2 : ∀ y ∈ (S : Subgroup ↥W), ∃ k : ℕ, ((y : ↥W) : G) ^ 2 ^ k = 1 := fun y hy => by
      obtain ⟨k, hk⟩ := S.2 ⟨y, hy⟩
      exact ⟨k, by simpa using congrArg (fun u : ↥(S : Subgroup ↥W) => ((u : ↥W) : G)) hk⟩
    obtain ⟨k₁, hk₁⟩ := h2 s hs
    have hsM : ((s : ↥W) : G) ∈ M := hM2 _ k₁ hk₁
    have hwk : ψ ((w : ↥W) : G) = 1 := (mem_inf.mp w.2).1
    have hwsM : ((w : ↥W) : G) * s * (w : G)⁻¹ ∈ M := hMn.conj_mem _ hsM _
    have hq : (QuotientGroup.mk (⟨_, hwsM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) =
        QuotientGroup.mk ⟨_, hsM⟩ := by
      rw [← UnbalancingLocal.conjQuotAction_mk' ((w : ↥W) : G) ⟨_, hsM⟩ hwsM, ← hψ, hwk,
        MulAut.one_apply]
    set u : ↥W := s⁻¹ * (w * s * w⁻¹) with hu
    have huS : u ∈ (S : Subgroup ↥W) := mul_mem (inv_mem hs) hs'
    obtain ⟨k, hk⟩ := h2 u huS
    have huM : ((u : ↥W) : G) ∈ M := hM2 _ k hk
    have hu1 : (⟨_, huM⟩ : ↥M) = 1 := by
      have hmem : (⟨_, huM⟩ : ↥M) ∈ pPrimeCore 2 ↥M := by
        rw [← QuotientGroup.eq_one_iff]
        have he : (⟨_, huM⟩ : ↥M) = (⟨_, hsM⟩ : ↥M)⁻¹ * ⟨_, hwsM⟩ := by
          apply Subtype.ext
          simp [hu, mul_assoc]
        rw [he, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hq, inv_mul_cancel]
      exact F3L57.eq_one_of_pow_two_pow_of_mem hOMo hmem (Subtype.ext (by simpa using hk))
    have hu1' : u = 1 := Subtype.ext (by simpa using congrArg Subtype.val hu1)
    rw [hu, inv_mul_eq_one] at hu1'
    calc s * w = w * s * w⁻¹ * w := by rw [← hu1']
      _ = w * s := by group
  have hW2 : ∀ x ∈ W, ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ D := fun x hx k hk =>
    ⟨hM2 x k hk, hWH hx⟩
  have hWle := le_sup_of_normalizer_le_centralizer hWH hWn hnc hW2
  intro h hh
  obtain ⟨d, hdD, hdk⟩ := hstep h hh
  have hw : d⁻¹ * h ∈ W := mem_inf.mpr ⟨hdk, mul_mem (inv_mem (mem_inf.mp hdD).2) hh⟩
  have h1 : h = d * (d⁻¹ * h) := by group
  rw [h1]
  exact mul_mem (mem_sup_right hdD) (hWle hw)

theorem lemma57_fourGroup_of_fix {z₁ z₂ : G} (hz₂ : orderOf z₂ = 2) {L K : Subgroup G}
    (hL : IsSolvableTwoComponentIn L (centralizer {z₁} ⊓ centralizer {z₂}))
    (hK₁ : K ≤ centralizer {z₁}) (hO : GH74.GLS.oPrimeResidualOf 2 L ≤ K)
    (hN : centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G)) (hz₂K : z₂ ∈ K)
    (hz₁K : z₁ ∈ K)
    (ha : OddAutInnerFix (↥K ⧸ pPrimeCore 2 ↥K) (QuotientGroup.mk ⟨z₁, hz₁K⟩)) :
    IsSolvableTwoComponentIn (L ⊓ K) (K ⊓ centralizer {z₂}) ∧
      L = (pPrimeCore 2 ↥(centralizer {z₁} ⊓ centralizer {z₂} : Subgroup G)).map
        (centralizer {z₁} ⊓ centralizer {z₂} : Subgroup G).subtype ⊔ (L ⊓ K) ∧
      GH74.GLS.oPrimeResidualOf 2 L = GH74.GLS.oPrimeResidualOf 2 (L ⊓ K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set CW : Subgroup G := centralizer {z₁} ⊓ centralizer {z₂} with hCW
  set OW := (pPrimeCore 2 ↥CW).map CW.subtype with hOW
  obtain ⟨hLCW, hLs, hLO, hLiso⟩ := hL
  have hLN : L ≤ normalizer (K : Set G) := hLCW.trans hN
  have hOWL : OW ≤ L := by
    rw [hOW, ← hLO]
    exact map_subtype_le _
  set N : Subgroup G := K ⊓ centralizer {z₂} with hNdef
  have hNCW : N ≤ CW := le_inf (inf_le_left.trans hK₁) inf_le_right
  have hNn : (N.subgroupOf CW).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hNCW]
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    have hgK := mem_normalizer_iff.mp (hN hg) x
    have hgC : g ∈ centralizer ({z₂} : Set G) := (mem_inf.mp hg).2
    constructor
    · intro hx
      obtain ⟨hxK, hxz⟩ := mem_inf.mp hx
      exact mem_inf.mpr ⟨hgK.mp hxK, mul_mem (mul_mem hgC hxz) (inv_mem hgC)⟩
    · intro hx
      obtain ⟨hxK, hxz⟩ := mem_inf.mp hx
      have h1 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      refine mem_inf.mpr ⟨hgK.mpr hxK, ?_⟩
      rw [h1]
      exact mul_mem (mul_mem (inv_mem hgC) hxz) hgC
  set E := K ⊔ L with hE
  have hKE : K ≤ E := le_sup_left
  have hLE : L ≤ E := le_sup_right
  have hEN : E ≤ normalizer (K : Set G) := sup_le le_normalizer hLN
  have hEz₁ : E ≤ centralizer {z₁} := sup_le hK₁ (hLCW.trans inf_le_left)
  have hMn : (K.subgroupOf E).Normal := (normal_subgroupOf_iff_le_normalizer hKE).mpr hEN
  have hM2 : ∀ g : ↥E, ∀ k : ℕ, g ^ 2 ^ k = 1 → g ∈ K.subgroupOf E := fun g k hk =>
    mem_subgroupOf.mpr (mem_of_mem_sup_of_pow hLN hO g.2 (by
      simpa using congrArg Subtype.val hk))
  let eK : ↥(K.subgroupOf E) ≃* ↥K := subgroupOfEquivOfLe hKE
  let eX : ↥(K.subgroupOf E) ⧸ pPrimeCore 2 ↥(K.subgroupOf E) ≃* ↥K ⧸ pPrimeCore 2 ↥K :=
    QuotientGroup.congr _ _ eK (pPrimeCore_map_iso 2 eK)
  set z' : ↥E := ⟨z₂, hKE hz₂K⟩ with hz'
  have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact hz₂
  set c' : ↥E := ⟨z₁, hKE hz₁K⟩ with hc'
  have hc'K : c' ∈ K.subgroupOf E := mem_subgroupOf.mpr hz₁K
  have hcen : centralizer ({z'} : Set ↥E) ≤ centralizer {c'} := by
    intro x _
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hEz₁ x.2)
  have hec : eX (QuotientGroup.mk ⟨c', hc'K⟩) = QuotientGroup.mk ⟨z₁, hz₁K⟩ := rfl
  have ha' : OddAutInnerFix (↥(K.subgroupOf E) ⧸ pPrimeCore 2 ↥(K.subgroupOf E))
      (QuotientGroup.mk ⟨c', hc'K⟩) :=
    OddAutInnerFix.of_mulEquiv eX (by rw [hec]; exact ha)
  have hle := le_sup_pPrimeCore_of_autFix hM2 hc'K hcen ha' hz'2 (mem_subgroupOf.mpr hz₂K)
  set A : Subgroup G := centralizer {z₂} ⊓ E with hAdef
  have hAE : A ≤ E := inf_le_right
  have hCz : centralizer ({z'} : Set ↥E) = A.subgroupOf E := by
    rw [hAdef, inf_subgroupOf_right]
    ext x
    rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
      Subtype.ext_iff]
    rfl
  rw [hCz] at hle
  have hmap := map_mono (f := E.subtype) hle
  rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.mpr hAE,
    F3S7.map_pPrimeCore_subgroupOf hAE] at hmap
  set OA := (pPrimeCore 2 ↥A).map A.subtype with hOA
  have hKA : ((K.subgroupOf E) ⊓ A.subgroupOf E).map E.subtype ≤ K ⊓ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨mem_subgroupOf.mp hx.1, mem_subgroupOf.mp hx.2⟩
  have hA : A ≤ OA ⊔ (K ⊓ A) := hmap.trans (sup_le_sup_left hKA _)
  have hAeq : A = N ⊔ L := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxz, hxE⟩ := mem_inf.mp hx
      rw [hE, sup_comm, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hLN] at hxE
      obtain ⟨l, hl, k₀, hk₀, rfl⟩ := hxE
      have hlz : l ∈ centralizer ({z₂} : Set G) := (mem_inf.mp (hLCW hl)).2
      have hk₀z : k₀ ∈ centralizer ({z₂} : Set G) := by
        have h1 : k₀ = l⁻¹ * (l * k₀) := by group
        rw [h1]
        exact mul_mem (inv_mem hlz) hxz
      rw [sup_comm]
      exact mul_mem_sup hl ⟨hk₀, hk₀z⟩
    · exact sup_le (le_inf inf_le_right (inf_le_left.trans hKE))
        (le_inf (hLCW.trans inf_le_right) hLE)
  have hACW : A ≤ CW := by rw [hAeq]; exact sup_le hNCW hLCW
  have hAs : (A.subgroupOf CW).IsSubnormal := by
    rw [hAeq]
    exact isSubnormal_sup_of_normal hNCW hLCW hNn hLs
  have hOAW : OA ≤ OW := by
    rw [hOA, F3L57.map_pPrimeCore_eq_inf hACW hAs]
    exact inf_le_right
  have hLeq : L = OW ⊔ (L ⊓ K) := by
    apply le_antisymm
    · intro l hl
      have hlA : l ∈ A := by rw [hAeq]; exact mem_sup_right hl
      have hKAn : K ⊓ A ≤ normalizer (OA : Set G) :=
        inf_le_right.trans (F3L57.le_normalizer_map_subtype (pPrimeCore 2 ↥A))
      have hl' : l ∈ ((K ⊓ A ⊔ OA : Subgroup G) : Set G) := by
        rw [sup_comm]
        exact hA hlA
      rw [coe_mul_of_left_le_normalizer_right _ _ hKAn] at hl'
      obtain ⟨d, hd, o, ho, rfl⟩ := hl'
      have hoL : o ∈ L := hOWL (hOAW ho)
      have hdL : d ∈ L := by
        have h1 : d = d * o * o⁻¹ := by group
        rw [h1]
        exact mul_mem hl (inv_mem hoL)
      rw [sup_comm]
      exact mul_mem_sup ⟨hdL, hd.1⟩ (hOAW ho)
    · exact sup_le hOWL inf_le_left
  set J₁ := L ⊓ K with hJ₁def
  have hJ₁N : J₁ ≤ N := le_inf inf_le_right (inf_le_left.trans (hLCW.trans inf_le_right))
  have hJ₁CW : J₁ ≤ CW := hJ₁N.trans hNCW
  have hJ₁L : (J₁.subgroupOf L).Normal := by
    rw [hJ₁def, inf_comm, normal_subgroupOf_iff_le_normalizer_inf]
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    have hgK := mem_normalizer_iff.mp (hLN hg) x
    constructor
    · intro hx
      obtain ⟨hxK, hxL⟩ := mem_inf.mp (mem_inf.mp hx).1
      have hgx : g * x * g⁻¹ ∈ L := mul_mem (mul_mem hg hxL) (inv_mem hg)
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨hgK.mp hxK, hgx⟩, hgx⟩
    · intro hx
      obtain ⟨hxK, hxL⟩ := mem_inf.mp (mem_inf.mp hx).1
      have hxL' : x ∈ L := by
        have h1 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [h1]
        exact mul_mem (mul_mem (inv_mem hg) hxL) hg
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨hgK.mpr hxK, hxL'⟩, hxL'⟩
  have hJ₁sCW : (J₁.subgroupOf CW).IsSubnormal := by
    have hJ₁L' : ((J₁.subgroupOf CW).subgroupOf (L.subgroupOf CW)).Normal := by
      have heq : (J₁.subgroupOf CW).subgroupOf (L.subgroupOf CW) =
          (J₁.subgroupOf L).comap (subgroupOfEquivOfLe hLCW).toMonoidHom := by
        ext x
        exact Iff.rfl
      rw [heq]
      exact hJ₁L.comap _
    exact IsSubnormal.step _ _ (subgroupOf_mono CW inf_le_left) hLs hJ₁L'
  have hJ₁sN : (J₁.subgroupOf N).IsSubnormal := F3L57.isSubnormal_subgroupOf_of_le hNCW hJ₁sCW
  have hON : (pPrimeCore 2 ↥N).map N.subtype ≤ OW :=
    F3L57.map_pPrimeCore_le_of_normal hNCW hNn
  have hOJ₁ : (pPrimeCore 2 ↥J₁).map J₁.subtype = (pPrimeCore 2 ↥N).map N.subtype := by
    rw [F3L57.map_pPrimeCore_eq_inf hJ₁N hJ₁sN]
    refine inf_eq_right.mpr (le_inf (hON.trans hOWL) ?_)
    exact (map_subtype_le _).trans inf_le_left
  obtain ⟨-, -, -, ⟨esat⟩⟩ := F3.saturate hJ₁CW hJ₁sCW
  have hsup : J₁ ⊔ OW = L := by rw [sup_comm, ← hLeq]
  let eJ : ↥L ⧸ pPrimeCore 2 ↥L ≃* ↥J₁ ⧸ pPrimeCore 2 ↥J₁ :=
    (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hsup).symm
      (pPrimeCore_map_iso 2 _)).trans esat
  have hJ₁iso : Nonempty (↥J₁ ⧸ pPrimeCore 2 ↥J₁ ≃* PSL(2, ZMod 3)) ∨
      Nonempty (↥J₁ ⧸ pPrimeCore 2 ↥J₁ ≃* SL(2, ZMod 3)) := by
    rcases hLiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl ⟨eJ.symm.trans e⟩
    · exact Or.inr ⟨eJ.symm.trans e⟩
  have hO2 : GH74.GLS.oPrimeResidualOf 2 L = GH74.GLS.oPrimeResidualOf 2 J₁ := by
    simp only [GH74.GLS.oPrimeResidualOf, GH74.GLS.oPrimeResidual, MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, coe_subtype]
    constructor
    · rintro ⟨y, ⟨k, hk⟩, rfl⟩
      have hyK : (y : G) ∈ K := hO (by
        rw [Sol78.oPrimeResidualOf_eq_closure]
        exact subset_closure ⟨y.2, k, by simpa using congrArg Subtype.val hk⟩)
      exact ⟨⟨y, y.2, hyK⟩, ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩, rfl⟩
    · rintro ⟨y, ⟨k, hk⟩, rfl⟩
      exact ⟨⟨y, y.2.1⟩, ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩, rfl⟩
  exact ⟨⟨hJ₁N, hJ₁sN, hOJ₁, hJ₁iso⟩, hLeq, hO2⟩

theorem lemma57_fourGroup_map_of_fix {z₁ z₂ : G} (hz₂ : orderOf z₂ = 2) {L K : Subgroup G}
    (hL : IsSolvableTwoComponentIn L (centralizer {z₁} ⊓ centralizer {z₂}))
    (hK₁ : K ≤ centralizer {z₁}) (hO : GH74.GLS.oPrimeResidualOf 2 L ≤ K)
    (hN : centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G)) (hz₂K : z₂ ∈ K)
    (hz₁K : z₁ ∈ K)
    (ha : OddAutInnerFix (↥K ⧸ pPrimeCore 2 ↥K) (QuotientGroup.mk ⟨z₁, hz₁K⟩)) :
    IsSolvableTwoComponentIn (((L ⊓ K).subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)))
      (centralizer {(QuotientGroup.mk (⟨z₂, hz₂K⟩ : ↥K) : ↥K ⧸ pPrimeCore 2 ↥K)}) := by
  obtain ⟨h1, -, -⟩ := lemma57_fourGroup_of_fix hz₂ hL hK₁ hO hN hz₂K hz₁K ha
  have h2 := F3S7.isSolvableTwoComponentIn_subgroupOf h1.1 inf_le_left h1
  have hC : (K ⊓ centralizer {z₂}).subgroupOf K = centralizer {(⟨z₂, hz₂K⟩ : ↥K)} := by
    rw [inf_comm, inf_subgroupOf_right]
    ext x
    rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
      Subtype.ext_iff]
    rfl
  rw [hC] at h2
  exact F3L221.isSolvableTwoComponentIn_map_mk (by rw [Subgroup.orderOf_mk]; exact hz₂) h2

theorem lemma57_fourGroup_map_of_aut {z₁ z₂ : G} (hz₂ : orderOf z₂ = 2) {L K : Subgroup G}
    (hL : IsSolvableTwoComponentIn L (centralizer {z₁} ⊓ centralizer {z₂}))
    (hK₁ : K ≤ centralizer {z₁}) (hO : GH74.GLS.oPrimeResidualOf 2 L ≤ K)
    (hN : centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G)) (hz₂K : z₂ ∈ K)
    (hz₁K : z₁ ∈ K) (ha : OddAutInner (↥K ⧸ pPrimeCore 2 ↥K)) :
    IsSolvableTwoComponentIn (((L ⊓ K).subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)))
      (centralizer {(QuotientGroup.mk (⟨z₂, hz₂K⟩ : ↥K) : ↥K ⧸ pPrimeCore 2 ↥K)}) :=
  lemma57_fourGroup_map_of_fix hz₂ hL hK₁ hO hN hz₂K hz₁K (ha.fix _)

end P58b3

end CFSG.ComponentClassification.HarrisLit.T1
