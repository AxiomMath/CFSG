module

public import CFSG.GH74.GLS.LU.Local.Conj
public import CFSG.GH74.GLS.LU.Local.GenCore
public import CFSG.GH74.GLS.IVK.Lifted.Out
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.InvolutionFusion
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma19c
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.IVK.Prod.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Prop41
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Core
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed2
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerInvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_19
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeActionNontrivialTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character
public import CFSG.Walter.J1.Inv

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure GenSyl (G : Type) [Group G] (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G) : Prop where
  z_inv : orderOf z = 2
  z_mem : z ∈ (S : Subgroup G)
  comm_z : ∀ s ∈ (S : Subgroup G), s * z = z * s
  t_mem : t ∈ (S : Subgroup G)
  t_swap : K₁.map (MulAut.conj t).toMonoidHom = K₂
  u_mem : u ∈ (S : Subgroup G)
  u_norm : u ∈ normalizer (K₁ : Set G)
  u_sq : u * u = 1
  cs : ∀ s ∈ (S : Subgroup G), (∀ k ∈ K₁ ⊔ K₂, s * k = k * s) → s ∈ zpowers z

namespace GenSyl

variable {G : Type} [Group G] {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}

theorem S_le_Cz (h : GenSyl G z S K₁ K₂ t u) : (S : Subgroup G) ≤ Cz z := fun _ hs =>
  mem_centralizer_singleton_iff.mpr (h.comm_z _ hs)

theorem z_sq (h : GenSyl G z S K₁ K₂ t u) : z * z = 1 := by
  have : z ^ 2 = 1 := by rw [← h.z_inv]; exact pow_orderOf_eq_one z
  rwa [pow_two] at this

end GenSyl

theorem LUSyl.toGen {G : Type} [Group G] {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}
    (h : LUSyl G z S K₁ K₂ t u) : GenSyl G z S K₁ K₂ t u :=
  ⟨h.z_inv, h.z_mem, fun _ hs => h.comm_z hs, h.t_mem, h.t_swap, h.u_mem, h.u_norm, h.u_sq, h.cs⟩

theorem card_sylow_eq_of_le (S : Sylow 2 G) {C : Subgroup G} (hSC : (S : Subgroup G) ≤ C) :
    Nat.card ↥(S : Subgroup G) = 2 ^ (Nat.card ↥C).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Sylow.card_eq_multiplicity (S.subtype hSC)
  rw [Sylow.coe_subtype] at h
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv]
  exact h

omit [Finite G] in
theorem normal_subgroupOf_of_conj {L C : Subgroup G} (h : ∀ c ∈ C, ∀ l ∈ L, c * l * c⁻¹ ∈ L) :
    (L.subgroupOf C).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using h g g.2 n hn

abbrev Nz (z : G) (K₁ K₂ : Subgroup G) : Subgroup G := A0 z ⊔ (K₁ ⊔ K₂)

variable {q : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}

omit [Finite G] in
theorem A0_conj {c : G} (hcz : c ∈ Cz z) {a : G} (ha : a ∈ A0 z) : c * a * c⁻¹ ∈ A0 z :=
  (mem_normalizer_iff.mp (mem_normalizer_pPrimeCoreOf hcz) a).mp ha

theorem Nz_conj (hc : LUComps G q z K₁ K₂) {c : G} (hcz : c ∈ Cz z) {n : G}
    (hn : n ∈ Nz z K₁ K₂) : c * n * c⁻¹ ∈ Nz z K₁ K₂ := by
  have h1 : (Nz z K₁ K₂).map (MulAut.conj c).toMonoidHom ≤ Nz z K₁ K₂ := by
    rw [Subgroup.map_sup]
    refine sup_le (le_trans ?_ le_sup_left) (le_trans ?_ le_sup_right)
    · rintro _ ⟨a, ha, rfl⟩; exact A0_conj hcz ha
    · rintro _ ⟨k, hk, rfl⟩; exact hc.conj_sup_mem hcz hk
  exact h1 ⟨n, hn, by simp [MulAut.conj_apply]⟩


omit [Finite G] in
theorem exists_orderOf_eq_two_pow_of_mem_sylow {S : Sylow 2 G} {x : G} (hx : x ∈ (S : Subgroup G)) :
    ∃ n : ℕ, orderOf x = 2 ^ n := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨x, hx⟩
  exact ⟨n, by rw [← hn]; exact (Subgroup.orderOf_mk x hx).symm⟩

theorem A0_comm [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂) {a k : G} (ha : a ∈ A0 z)
    (hk : k ∈ K₁ ⊔ K₂) : a * k = k * a :=
  mem_centralizer_iff.mp (hc.le_centralizer_A0 hk) a ha

theorem two_elt_mem_K [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂) {x : G}
    (hx : x ∈ Nz z K₁ K₂) {n : ℕ} (hord : orderOf x = 2 ^ n) : x ∈ K₁ ⊔ K₂ := by
  obtain ⟨a, ha, k, hk, rfl⟩ := mem_sup_of_commute (fun a ha k hk => A0_comm hc ha hk) hx
  have hcomm : Commute a k := A0_comm hc ha hk
  have h1 : (a * k) ^ (2 ^ n) = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  rw [hcomm.mul_pow] at h1
  have h2 : a ^ (2 ^ n) ∈ K₁ ⊔ K₂ := by
    have : a ^ (2 ^ n) = (k ^ (2 ^ n))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]; exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hk _)
  have hcop : (2 ^ n).gcd (orderOf a) = 1 := by
    have := (Nat.coprime_two_left.mpr (odd_orderOf_A0 ha))
    exact (Nat.Coprime.pow_left n this)
  have h3 : a ∈ zpowers (a ^ (2 ^ n)) := mem_zpowers_pow_iff.mpr hcop
  have h4 : a ∈ K₁ ⊔ K₂ := by
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h3
    rw [← hi]; exact Subgroup.zpow_mem _ h2 i
  exact Subgroup.mul_mem _ h4 hk

theorem S_inf_Nz [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂) :
    (S : Subgroup G) ⊓ Nz z K₁ K₂ = (S : Subgroup G) ⊓ (K₁ ⊔ K₂) := by
  apply le_antisymm
  · rintro x ⟨hxS, hxN⟩
    obtain ⟨n, hn⟩ := exists_orderOf_eq_two_pow_of_mem_sylow hxS
    exact ⟨hxS, two_elt_mem_K hc hxN hn⟩
  · exact inf_le_inf_left _ le_sup_right


omit [Finite G] in
theorem K_le_Cz (hc : LUComps G q z K₁ K₂) : K₁ ⊔ K₂ ≤ Cz z := sup_le hc.comp₁.1 hc.comp₂.1

omit [Finite G] in
theorem A0_le_Cz : A0 z ≤ Cz z := Subgroup.map_subtype_le _

omit [Finite G] in
theorem Nz_le_Cz (hc : LUComps G q z K₁ K₂) : Nz z K₁ K₂ ≤ Cz z :=
  sup_le A0_le_Cz (K_le_Cz hc)

theorem K₁_conj_mem (hc : LUComps G q z K₁ K₂) {c l : G} (hcK : c ∈ K₁ ⊔ K₂) (hl : l ∈ K₁) :
    c * l * c⁻¹ ∈ K₁ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc.comm hcK
  have hbl : b * l = l * b := (hc.comm l hl b hb).symm
  have : a * b * l * (a * b)⁻¹ = a * l * a⁻¹ := by
    calc a * b * l * (a * b)⁻¹ = a * (b * l) * b⁻¹ * a⁻¹ := by group
      _ = a * (l * b) * b⁻¹ * a⁻¹ := by rw [hbl]
      _ = a * l * a⁻¹ := by group
  rw [this]; exact K₁.mul_mem (K₁.mul_mem ha hl) (K₁.inv_mem ha)

theorem K₂_conj_mem (hc : LUComps G q z K₁ K₂) {c l : G} (hcK : c ∈ K₁ ⊔ K₂) (hl : l ∈ K₂) :
    c * l * c⁻¹ ∈ K₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc.comm hcK
  have hal : a * (b * l * b⁻¹) = (b * l * b⁻¹) * a :=
    hc.comm a ha _ (K₂.mul_mem (K₂.mul_mem hb hl) (K₂.inv_mem hb))
  have : a * b * l * (a * b)⁻¹ = b * l * b⁻¹ := by
    calc a * b * l * (a * b)⁻¹ = a * (b * l * b⁻¹) * a⁻¹ := by group
      _ = (b * l * b⁻¹) * a * a⁻¹ := by rw [hal]
      _ = b * l * b⁻¹ := by group
  rw [this]; exact K₂.mul_mem (K₂.mul_mem hb hl) (K₂.inv_mem hb)

theorem card_Q [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂) (hs : GenSyl G z S K₁ K₂ t u) :
    Nat.card ↥((S : Subgroup G) ⊓ (K₁ ⊔ K₂)) = 2 ^ (Nat.card ↥(K₁ ⊔ K₂)).factorization 2 :=
  card_inf_of_sylow_of_normal 2 hs.S_le_Cz (card_sylow_eq_of_le S hs.S_le_Cz) (K_le_Cz hc)
    (normal_subgroupOf_of_conj (fun _ hc' _ hl => hc.conj_sup_mem hc' hl))

theorem card_Q₁ [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂) (hs : GenSyl G z S K₁ K₂ t u) :
    Nat.card ↥((S : Subgroup G) ⊓ K₁) = 2 ^ (Nat.card ↥K₁).factorization 2 := by
  have h := card_inf_of_sylow_of_normal 2 (M := K₁ ⊔ K₂) (P := (S : Subgroup G) ⊓ (K₁ ⊔ K₂))
    (L := K₁) inf_le_right (card_Q hc hs) le_sup_left
    (normal_subgroupOf_of_conj (fun _ hc' _ hl => K₁_conj_mem hc hc' hl))
  have e : (S : Subgroup G) ⊓ (K₁ ⊔ K₂) ⊓ K₁ = (S : Subgroup G) ⊓ K₁ := by
    ext x
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, Subgroup.mem_sup_left h3⟩, h3⟩
  rwa [e] at h

theorem card_Q₂ [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂) (hs : GenSyl G z S K₁ K₂ t u) :
    Nat.card ↥((S : Subgroup G) ⊓ K₂) = 2 ^ (Nat.card ↥K₂).factorization 2 := by
  have h := card_inf_of_sylow_of_normal 2 (M := K₁ ⊔ K₂) (P := (S : Subgroup G) ⊓ (K₁ ⊔ K₂))
    (L := K₂) inf_le_right (card_Q hc hs) le_sup_right
    (normal_subgroupOf_of_conj (fun _ hc' _ hl => K₂_conj_mem hc hc' hl))
  have e : (S : Subgroup G) ⊓ (K₁ ⊔ K₂) ⊓ K₂ = (S : Subgroup G) ⊓ K₂ := by
    ext x
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, Subgroup.mem_sup_right h3⟩, h3⟩
  rwa [e] at h

theorem card_K_mul_two [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂) (hs : GenSyl G z S K₁ K₂ t u) :
    Nat.card ↥(K₁ ⊔ K₂) * 2 = Nat.card ↥K₁ * Nat.card ↥K₂ := by
  have h := card_sup_mul_card_inf_of_commute hc.comm
  rw [hc.inf_eq, Nat.card_zpowers, hs.z_inv] at h
  exact h

theorem Q_eq_sup [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂) (hs : GenSyl G z S K₁ K₂ t u) :
    (S : Subgroup G) ⊓ (K₁ ⊔ K₂) = ((S : Subgroup G) ⊓ K₁) ⊔ ((S : Subgroup G) ⊓ K₂) := by
  have hle : ((S : Subgroup G) ⊓ K₁) ⊔ ((S : Subgroup G) ⊓ K₂) ≤ (S : Subgroup G) ⊓ (K₁ ⊔ K₂) :=
    sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  have hcomm : ∀ a ∈ (S : Subgroup G) ⊓ K₁, ∀ b ∈ (S : Subgroup G) ⊓ K₂, a * b = b * a :=
    fun a ha b hb => hc.comm a ha.2 b hb.2
  have h1 := card_sup_mul_card_inf_of_commute hcomm
  have hzmem : ∀ x : G, x ∈ ((S : Subgroup G) ⊓ K₁) ⊓ ((S : Subgroup G) ⊓ K₂) ↔ x ∈ zpowers z := by
    intro x
    constructor
    · rintro ⟨⟨_, hx1⟩, ⟨_, hx2⟩⟩
      rw [← hc.inf_eq]; exact ⟨hx1, hx2⟩
    · intro hx
      have hx' : x ∈ K₁ ⊓ K₂ := by rw [hc.inf_eq]; exact hx
      have hxS : x ∈ (S : Subgroup G) := (zpowers_le.mpr hs.z_mem) hx
      exact ⟨⟨hxS, hx'.1⟩, ⟨hxS, hx'.2⟩⟩
  have e : ((S : Subgroup G) ⊓ K₁) ⊓ ((S : Subgroup G) ⊓ K₂) = zpowers z := by
    ext x; exact hzmem x
  rw [e, Nat.card_zpowers, hs.z_inv, card_Q₁ hc hs, card_Q₂ hc hs] at h1
  rw [card_Q hc hs]
  have hKne : Nat.card ↥K₁ ≠ 0 := Nat.card_pos.ne'
  have hK2ne : Nat.card ↥K₂ ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card ↥(K₁ ⊔ K₂)).factorization 2 + 1 =
      (Nat.card ↥K₁).factorization 2 + (Nat.card ↥K₂).factorization 2 := by
    have := congrArg (fun n => n.factorization 2) (card_K_mul_two hc hs)
    have h22 : (Nat.factorization 2) 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
    rw [Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Nat.factorization_mul hKne hK2ne,
      Finsupp.add_apply, Finsupp.add_apply, h22] at this
    omega
  have h2 : Nat.card ↥(((S : Subgroup G) ⊓ K₁) ⊔ ((S : Subgroup G) ⊓ K₂)) * 2 =
      2 ^ ((Nat.card ↥(K₁ ⊔ K₂)).factorization 2 + 1) := by
    rw [hfac, pow_add]
    exact h1
  rw [pow_succ] at h2
  omega


omit [Finite G] in
theorem le_A0_of_normal_odd {N : Subgroup G} (hNC : N ≤ Cz z)
    (hnorm : ∀ c ∈ Cz z, ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hcop : Nat.Coprime 2 (Nat.card N)) :
    N ≤ A0 z := by
  have hn : (N.subgroupOf (Cz z)).Normal := normal_subgroupOf_of_conj hnorm
  have hcop' : Nat.Coprime 2 (Nat.card ↥(N.subgroupOf (Cz z))) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv]
  have hle : N.subgroupOf (Cz z) ≤ pPrimeCore 2 ↥(Cz z) := le_sSup ⟨hn, hcop'⟩
  intro a ha
  exact ⟨⟨a, hNC ha⟩, hle (show (⟨a, hNC ha⟩ : ↥(Cz z)) ∈ N.subgroupOf (Cz z) from ha), rfl⟩

abbrev Dz (z : G) (K₁ K₂ : Subgroup G) : Subgroup G :=
  Cz z ⊓ centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)

omit [Finite G] in
theorem Dz_le_Cz : Dz z K₁ K₂ ≤ Cz z := inf_le_left

theorem Dz_conj (hc : LUComps G q z K₁ K₂) {c d : G} (hcz : c ∈ Cz z) (hd : d ∈ Dz z K₁ K₂) :
    c * d * c⁻¹ ∈ Dz z K₁ K₂ := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hcz hd.1) (Subgroup.inv_mem _ hcz), ?_⟩
  refine mem_centralizer_iff.mpr ?_
  intro k hk
  have hk' : c⁻¹ * k * c⁻¹⁻¹ ∈ K₁ ⊔ K₂ := hc.conj_sup_mem (Subgroup.inv_mem _ hcz) hk
  have h1 := mem_centralizer_iff.mp hd.2 _ hk'
  have h2 : (c⁻¹ * k * c⁻¹⁻¹) * d = d * (c⁻¹ * k * c⁻¹⁻¹) := h1
  simp only [inv_inv] at h2
  calc k * (c * d * c⁻¹) = c * ((c⁻¹ * k * c) * d) * c⁻¹ := by group
    _ = c * (d * (c⁻¹ * k * c)) * c⁻¹ := by rw [h2]
    _ = (c * d * c⁻¹) * k := by group

omit [Finite G] in
theorem S_inf_Dz [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂) (hs : GenSyl G z S K₁ K₂ t u) :
    (S : Subgroup G) ⊓ Dz z K₁ K₂ = zpowers z := by
  apply le_antisymm
  · rintro x ⟨hxS, hxC, hxK⟩
    exact hs.cs x hxS (fun k hk => (mem_centralizer_iff.mp hxK k hk).symm)
  · rw [zpowers_le]
    refine ⟨hs.z_mem, mem_centralizer_singleton_iff.mpr rfl, ?_⟩
    refine mem_centralizer_iff.mpr ?_
    intro k hk
    exact mem_centralizer_singleton_iff.mp (K_le_Cz hc hk)

theorem card_Dz_two [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂) (hs : GenSyl G z S K₁ K₂ t u) :
    (Nat.card ↥(Dz z K₁ K₂)).factorization 2 = 1 := by
  have h := card_inf_of_sylow_of_normal 2 hs.S_le_Cz (card_sylow_eq_of_le S hs.S_le_Cz)
    (Dz_le_Cz (z := z) (K₁ := K₁) (K₂ := K₂))
    (normal_subgroupOf_of_conj (fun _ hc' _ hl => Dz_conj hc hc' hl))
  rw [S_inf_Dz hc hs, Nat.card_zpowers, hs.z_inv] at h
  have h2 : (2 : ℕ) ^ 1 = 2 ^ (Nat.card ↥(Dz z K₁ K₂)).factorization 2 := by simpa using h
  exact (Nat.pow_right_injective le_rfl h2).symm

theorem Dz_decomp [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂) (hs : GenSyl G z S K₁ K₂ t u)
    {d : G} (hd : d ∈ Dz z K₁ K₂) : ∃ a ∈ A0 z, ∃ i : ℤ, d = a * z ^ i := by
  obtain ⟨O, hOn, hOi, hOodd, hOchar⟩ := exists_oddOrder_index_two (D := ↥(Dz z K₁ K₂))
    (card_Dz_two hc hs)
  set O' : Subgroup G := O.map (Dz z K₁ K₂).subtype with hO'
  have hO'mem : ∀ x : G, x ∈ O' ↔ ∃ hx : x ∈ Dz z K₁ K₂, Odd (orderOf x) := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have := (hOchar y).mp hy
      rwa [← Subgroup.orderOf_coe] at this
    · rintro ⟨hx, hodd⟩
      refine ⟨⟨x, hx⟩, (hOchar _).mpr ?_, rfl⟩
      rwa [Subgroup.orderOf_mk]
  have hO'A : O' ≤ A0 z := by
    refine le_A0_of_normal_odd ?_ ?_ ?_
    · rintro x ⟨y, -, rfl⟩; exact y.2.1
    · intro c hcz n hn
      obtain ⟨hnD, hnodd⟩ := (hO'mem n).mp hn
      rw [hO'mem]
      refine ⟨Dz_conj hc hcz hnD, ?_⟩
      have : orderOf (c * n * c⁻¹) = orderOf n := by
        have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective n
        simpa [MulAut.conj_apply] using this
      rw [this]; exact hnodd
    · have : Nat.card O' = Nat.card O := Subgroup.card_map_of_injective (Dz z K₁ K₂).subtype_injective
      rw [this]
      exact Nat.coprime_two_left.mpr hOodd
  have hzD : z ∈ Dz z K₁ K₂ := by
    have := (zpowers_le.mp (S_inf_Dz hc hs).ge)
    exact this.2
  have hzO : (⟨z, hzD⟩ : ↥(Dz z K₁ K₂)) ∉ O := by
    intro h
    have := (hOchar _).mp h
    rw [Subgroup.orderOf_mk, hs.z_inv] at this
    exact absurd this (by decide)
  by_cases hdO : (⟨d, hd⟩ : ↥(Dz z K₁ K₂)) ∈ O
  · exact ⟨d, hO'A ⟨⟨d, hd⟩, hdO, rfl⟩, 0, by simp⟩
  · have hdzO : (⟨d, hd⟩ : ↥(Dz z K₁ K₂)) * ⟨z, hzD⟩ ∈ O :=
      (Subgroup.mul_mem_iff_of_index_two hOi).mpr (iff_of_false hdO hzO)
    refine ⟨d * z, hO'A ⟨_, hdzO, rfl⟩, -1, ?_⟩
    rw [zpow_neg_one]
    group


theorem aut_comm_inner {K : Type} [Group K] {F : Type} [Field F] [Finite F]
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (α β : MulAut K) :
    ∃ k : K, α * β * α⁻¹ * β⁻¹ = MulAut.conj k := by
  obtain ⟨s, hs⟩ := CFSG.GH74.GLS.IVK.Lifted.out_abelian_sl hodd h3 (MulAut.congr e α)
    (MulAut.congr e β)
  refine ⟨e.symm s, ?_⟩
  apply (MulAut.congr e).injective
  have hc : (MulAut.congr e) (MulAut.conj (e.symm s)) = MulAut.conj s := by
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  rw [hc]
  simp only [map_mul, map_inv]
  exact hs.symm

omit [Finite G] in
theorem normalizerMonoidHom_coe (K : Subgroup G) (c : normalizer (K : Set G)) (x : ↥K) :
    ((K.normalizerMonoidHom c x : ↥K) : G) = (c : G) * x * (c : G)⁻¹ := by
  simp


omit [Finite G] in
theorem comm_acts_inner {K : Subgroup G} {F : Type} [Field F] [Finite F]
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    {c d : G} (hc : c ∈ normalizer (K : Set G)) (hd : d ∈ normalizer (K : Set G)) :
    ∃ k ∈ K, ∀ x ∈ K, (c * d * c⁻¹ * d⁻¹) * x * (c * d * c⁻¹ * d⁻¹)⁻¹ = k * x * k⁻¹ := by
  set γ : normalizer (K : Set G) := ⟨c, hc⟩ * ⟨d, hd⟩ * ⟨c, hc⟩⁻¹ * ⟨d, hd⟩⁻¹ with hγ
  have hγG : (γ : G) = c * d * c⁻¹ * d⁻¹ := by simp [hγ]
  obtain ⟨k, hk⟩ := aut_comm_inner e hodd h3 (K.normalizerMonoidHom ⟨c, hc⟩)
    (K.normalizerMonoidHom ⟨d, hd⟩)
  have hk' : K.normalizerMonoidHom γ = MulAut.conj k := by
    rw [hγ]; simp only [map_mul, map_inv]; exact hk
  refine ⟨k, k.2, fun x hx => ?_⟩
  have := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : G)) hk'
  simp only [normalizerMonoidHom_coe, MulAut.conj_apply, hγG] at this
  simpa using this


abbrev C1z (z : G) (K₁ : Subgroup G) : Subgroup G := Cz z ⊓ normalizer (K₁ : Set G)

theorem C1_normalizer₂ (hc : LUComps G q z K₁ K₂) {c : G} (hc1 : c ∈ C1z z K₁) :
    c ∈ normalizer (K₂ : Set G) := by
  rcases hc.perm hc1.1 with ⟨_, e2⟩ | ⟨e1, _⟩
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr e2
  · exfalso
    have := Subgroup.mem_normalizer_iff_map_conj_eq.mp hc1.2
    exact hc.ne (this.symm.trans e1)

omit [Finite G] in
theorem K₁_le_Nz : K₁ ≤ Nz z K₁ K₂ := le_sup_left.trans le_sup_right
omit [Finite G] in
theorem K₂_le_Nz : K₂ ≤ Nz z K₁ K₂ := le_sup_right.trans le_sup_right
omit [Finite G] in
theorem A0_le_Nz : A0 z ≤ Nz z K₁ K₂ := le_sup_left

theorem commutator_mem_Nz [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂)
    (hs : GenSyl G z S K₁ K₂ t u) (hodd : Odd q) (h5 : 5 ≤ q) {c d : G} (hc1 : c ∈ C1z z K₁)
    (hd1 : d ∈ C1z z K₁) : c * d * c⁻¹ * d⁻¹ ∈ Nz z K₁ K₂ := by
  obtain ⟨F₁, _, _, hF₁, ⟨e₁⟩⟩ := hc.sl₁
  obtain ⟨F₂, _, _, hF₂, ⟨e₂⟩⟩ := hc.sl₂
  have hodd₁ : Odd (Nat.card F₁) := by rw [hF₁]; exact hodd
  have hodd₂ : Odd (Nat.card F₂) := by rw [hF₂]; exact hodd
  have h3₁ : 3 < Nat.card F₁ := by rw [hF₁]; omega
  have h3₂ : 3 < Nat.card F₂ := by rw [hF₂]; omega
  obtain ⟨k₁, hk₁, hk₁x⟩ := comm_acts_inner
    (e₁.trans (specialLinearGroupEquivStatedSL 2 F₁).symm) hodd₁ h3₁ hc1.2 hd1.2
  obtain ⟨k₂, hk₂, hk₂x⟩ := comm_acts_inner
    (e₂.trans (specialLinearGroupEquivStatedSL 2 F₂).symm) hodd₂ h3₂ (C1_normalizer₂ hc hc1)
    (C1_normalizer₂ hc hd1)
  set g := c * d * c⁻¹ * d⁻¹ with hg
  have hgC : g ∈ Cz z := by
    have hc' := hc1.1
    have hd' := hd1.1
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hc' hd') (Subgroup.inv_mem _ hc'))
      (Subgroup.inv_mem _ hd')
  have hk₁C : k₁ ∈ Cz z := K_le_Cz hc (Subgroup.mem_sup_left hk₁)
  have hk₂C : k₂ ∈ Cz z := K_le_Cz hc (Subgroup.mem_sup_right hk₂)
  set e' := (k₁ * k₂)⁻¹ * g with he'
  have hk12 : k₁⁻¹ * k₂ = k₂ * k₁⁻¹ := (hc.comm _ (Subgroup.inv_mem _ hk₁) _ hk₂)
  have hk12' : k₁⁻¹ * k₂⁻¹ = k₂⁻¹ * k₁⁻¹ := hc.comm _ (Subgroup.inv_mem _ hk₁) _ (Subgroup.inv_mem _ hk₂)
  have hcen₁ : K₁ ≤ centralizer ({e'} : Set G) := by
    intro x hx
    refine mem_centralizer_singleton_iff.mpr ?_
    have hgx : g * x = (k₁ * x * k₁⁻¹) * g := by
      have := hk₁x x hx
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = (k₁ * x * k₁⁻¹) * g := by rw [this]
    have hx2 : k₂⁻¹ * x = x * k₂⁻¹ := (hc.comm x hx _ (Subgroup.inv_mem _ hk₂)).symm
    calc x * e' = x * ((k₁ * k₂)⁻¹ * g) := rfl
      _ = x * k₂⁻¹ * k₁⁻¹ * g := by group
      _ = k₂⁻¹ * x * k₁⁻¹ * g := by rw [hx2]
      _ = (k₁ * k₂)⁻¹ * ((k₁ * x * k₁⁻¹) * g) := by group
      _ = (k₁ * k₂)⁻¹ * (g * x) := by rw [hgx]
      _ = e' * x := by rw [he']; group
  have hcen₂ : K₂ ≤ centralizer ({e'} : Set G) := by
    intro x hx
    refine mem_centralizer_singleton_iff.mpr ?_
    have hgx : g * x = (k₂ * x * k₂⁻¹) * g := by
      have := hk₂x x hx
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = (k₂ * x * k₂⁻¹) * g := by rw [this]
    have h1x : k₁⁻¹ * x = x * k₁⁻¹ := (hc.comm _ (Subgroup.inv_mem _ hk₁) x hx)
    calc x * e' = x * ((k₁ * k₂)⁻¹ * g) := rfl
      _ = x * k₂⁻¹ * k₁⁻¹ * g := by group
      _ = x * (k₂⁻¹ * k₁⁻¹) * g := by group
      _ = x * (k₁⁻¹ * k₂⁻¹) * g := by rw [hk12']
      _ = (x * k₁⁻¹) * k₂⁻¹ * g := by group
      _ = (k₁⁻¹ * x) * k₂⁻¹ * g := by rw [h1x]
      _ = k₂⁻¹ * (k₁⁻¹ * k₂) * x * k₂⁻¹ * g := by
          rw [hk12]; group
      _ = (k₁ * k₂)⁻¹ * ((k₂ * x * k₂⁻¹) * g) := by group
      _ = (k₁ * k₂)⁻¹ * (g * x) := by rw [hgx]
      _ = e' * x := by rw [he']; group
  have hKcen : K₁ ⊔ K₂ ≤ centralizer ({e'} : Set G) := sup_le hcen₁ hcen₂
  have he'D : e' ∈ Dz z K₁ K₂ := by
    refine ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hk₁C hk₂C)) hgC
    · refine mem_centralizer_iff.mpr ?_
      intro k hk
      exact mem_centralizer_singleton_iff.mp (hKcen hk)
  obtain ⟨a, ha, i, hai⟩ := Dz_decomp hc hs he'D
  have hgeq : g = k₁ * k₂ * (a * z ^ i) := by
    rw [← hai, he']; group
  rw [hgeq]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (K₁_le_Nz hk₁) (K₂_le_Nz hk₂)) (Subgroup.mul_mem _ (A0_le_Nz ha) (Subgroup.zpow_mem _ (K₁_le_Nz hc.z_mem₁) i))


omit [Finite G] in
theorem mem_map_conj_iff {K : Subgroup G} {c x : G} :
    x ∈ K.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * x * c ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show c⁻¹ * (c * y * c⁻¹) * c = y by group]
    exact hy
  · intro h
    refine ⟨c⁻¹ * x * c, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem C1z_normal (hc : LUComps G q z K₁ K₂) {c l : G} (hcz : c ∈ Cz z) (hl : l ∈ C1z z K₁) :
    c * l * c⁻¹ ∈ C1z z K₁ := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hcz hl.1) (Subgroup.inv_mem _ hcz), ?_⟩
  have hl₂ := C1_normalizer₂ hc hl
  refine mem_normalizer_iff.mpr ?_
  intro x
  rcases hc.perm hcz with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have hmem : ∀ y, y ∈ K₁ ↔ c⁻¹ * y * c ∈ K₁ := by
      intro y; rw [← mem_map_conj_iff, e1]
    calc x ∈ K₁ ↔ c⁻¹ * x * c ∈ K₁ := hmem x
      _ ↔ l * (c⁻¹ * x * c) * l⁻¹ ∈ K₁ := mem_normalizer_iff.mp hl.2 _
      _ ↔ c * l * c⁻¹ * x * (c * l * c⁻¹)⁻¹ ∈ K₁ := by
        rw [hmem (c * l * c⁻¹ * x * (c * l * c⁻¹)⁻¹)]
        have : c⁻¹ * (c * l * c⁻¹ * x * (c * l * c⁻¹)⁻¹) * c = l * (c⁻¹ * x * c) * l⁻¹ := by group
        rw [this]
  · have hmem₁ : ∀ y, y ∈ K₁ ↔ c⁻¹ * y * c ∈ K₂ := by
      intro y; rw [← mem_map_conj_iff, e2]
    have hmem₂ : ∀ y, y ∈ K₂ ↔ c⁻¹ * y * c ∈ K₁ := by
      intro y; rw [← mem_map_conj_iff, e1]
    calc x ∈ K₁ ↔ c⁻¹ * x * c ∈ K₂ := hmem₁ x
      _ ↔ l * (c⁻¹ * x * c) * l⁻¹ ∈ K₂ := mem_normalizer_iff.mp hl₂ _
      _ ↔ c * l * c⁻¹ * x * (c * l * c⁻¹)⁻¹ ∈ K₁ := by
        rw [hmem₁ (c * l * c⁻¹ * x * (c * l * c⁻¹)⁻¹)]
        have : c⁻¹ * (c * l * c⁻¹ * x * (c * l * c⁻¹)⁻¹) * c = l * (c⁻¹ * x * c) * l⁻¹ := by group
        rw [this]

omit [Finite G] in
theorem C1z_le_Cz : C1z z K₁ ≤ Cz z := inf_le_left

theorem card_S1 [IsCyclic ↥(A0 z)] (hs : GenSyl G z S K₁ K₂ t u) (hc : LUComps G q z K₁ K₂) :
    Nat.card ↥((S : Subgroup G) ⊓ C1z z K₁) = 2 ^ (Nat.card ↥(C1z z K₁)).factorization 2 :=
  card_inf_of_sylow_of_normal 2 hs.S_le_Cz (card_sylow_eq_of_le S hs.S_le_Cz) C1z_le_Cz
    (normal_subgroupOf_of_conj (fun _ hc' _ hl => C1z_normal hc hc' hl))


theorem Nz_card_sylow [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂) (hs : GenSyl G z S K₁ K₂ t u) :
    Nat.card ↥((S : Subgroup G) ⊓ (K₁ ⊔ K₂)) = 2 ^ (Nat.card ↥(Nz z K₁ K₂)).factorization 2 := by
  have h := card_inf_of_sylow_of_normal 2 hs.S_le_Cz (card_sylow_eq_of_le S hs.S_le_Cz)
    (Nz_le_Cz hc) (normal_subgroupOf_of_conj (fun _ hc' _ hl => Nz_conj hc hc' hl))
  rwa [S_inf_Nz hc] at h

theorem frattini_Q [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂) (hs : GenSyl G z S K₁ K₂ t u)
    {c : G} (hcz : c ∈ Cz z) :
    ∃ n ∈ Nz z K₁ K₂,
      n⁻¹ * c ∈ normalizer (((S : Subgroup G) ⊓ (K₁ ⊔ K₂) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup G := (S : Subgroup G) ⊓ (K₁ ⊔ K₂) with hQ
  set T : Subgroup G := Q.map (MulAut.conj c).toMonoidHom with hT
  have hQN : Q ≤ Nz z K₁ K₂ := inf_le_right.trans le_sup_right
  have hTN : T ≤ Nz z K₁ K₂ := by
    rintro _ ⟨y, hy, rfl⟩
    have := Nz_conj hc hcz (hQN hy)
    simpa [MulAut.conj_apply] using this
  have hcard : Nat.card ↥T = Nat.card ↥Q := card_map_conj Q c
  have hTp : IsPGroup 2 ↥T := IsPGroup.of_card (n := (Nat.card ↥(K₁ ⊔ K₂)).factorization 2)
    (by rw [hcard]; exact card_Q hc hs)
  obtain ⟨n, hn, hnT⟩ := exists_mem_conj_eq_of_sylow 2 hQN (Nz_card_sylow hc hs) hTN hTp hcard.ge
  refine ⟨n, hn, ?_⟩
  refine mem_normalizer_iff.mpr (fun y => ?_)
  have h1 : y ∈ Q ↔ c * y * c⁻¹ ∈ T := by
    rw [hT, mem_map_conj_iff]
    have : c⁻¹ * (c * y * c⁻¹) * c = y := by group
    rw [this]
  rw [h1, hnT]
  have : (n : G)⁻¹ * (c * y * c⁻¹) * n = (n⁻¹ * c) * y * (n⁻¹ * c)⁻¹ := by group
  rw [this]

theorem two_elt_mem_N_S1 [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂)
    (hs : GenSyl G z S K₁ K₂ t u) (hodd : Odd q) (h5 : 5 ≤ q) {w : G} (hw : w ∈ C1z z K₁) {k : ℕ}
    (hord : orderOf w = 2 ^ k) :
    ∃ n ∈ Nz z K₁ K₂, ∃ s ∈ (S : Subgroup G) ⊓ C1z z K₁, w = n * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg, hgs⟩ := exists_conj_mem_of_sylow 2 (inf_le_right : (S : Subgroup G) ⊓ C1z z K₁ ≤ C1z z K₁)
    (card_S1 hs hc) hw ⟨k, hord⟩
  refine ⟨(g : G) * ((g : G)⁻¹ * w * g) * (g : G)⁻¹ * ((g : G)⁻¹ * w * g)⁻¹, ?_, _, hgs, ?_⟩
  · exact commutator_mem_Nz hc hs hodd h5 hg hgs.2
  · group


@[expose] def SL2SylowLeaf : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (q : ℕ), HasSL2Model K (fun r => r = q) → Odd q → 5 ≤ q →
    ∀ Q : Subgroup K, Nat.card ↥Q = 2 ^ (Nat.card K).factorization 2 →
      (∀ x : K, (∀ y ∈ Q, x * y = y * x) → x ∈ Subgroup.center K) ∧
      ∀ α : MulAut K, Odd (orderOf α) → (∀ x : K, x ∈ Q ↔ α x ∈ Q) →
        ∃ g ∈ normalizer (Q : Set K), ∀ x ∈ Q, α x = g * x * g⁻¹

theorem adjust_component (hK : SL2SylowLeaf) {K : Subgroup G} {q : ℕ}
    (hmod : HasSL2Model ↥K (fun r => r = q)) (hodd : Odd q) (h5 : 5 ≤ q)
    {R : Subgroup G} (hRK : R ≤ K) (hR : Nat.card ↥R = 2 ^ (Nat.card ↥K).factorization 2)
    {v : G} (hvK : v ∈ normalizer (K : Set G)) (hvodd : Odd (orderOf v))
    (hvR : ∀ x, x ∈ R ↔ v * x * v⁻¹ ∈ R) :
    ∃ g ∈ K, ∀ x ∈ R, v * x * v⁻¹ = g * x * g⁻¹ := by
  set α := K.normalizerMonoidHom ⟨v, hvK⟩ with hα
  have hαodd : Odd (orderOf α) := by
    have h1 := orderOf_map_dvd K.normalizerMonoidHom (⟨v, hvK⟩ : normalizer (K : Set G))
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hvodd h1
  have hcard : Nat.card ↥(R.subgroupOf K) = 2 ^ (Nat.card ↥K).factorization 2 := by
    rw [← hR]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv
  have hpres : ∀ x : ↥K, x ∈ R.subgroupOf K ↔ α x ∈ R.subgroupOf K := by
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hα, normalizerMonoidHom_coe]
    exact hvR x
  obtain ⟨g', -, hg'⟩ := ((hK ↥K q hmod hodd h5 (R.subgroupOf K) hcard).2) α hαodd hpres
  refine ⟨(g' : G), g'.2, fun x hx => ?_⟩
  have h1 := hg' ⟨x, hRK hx⟩ (by rw [Subgroup.mem_subgroupOf]; exact hx)
  have h2 := congrArg (fun y : ↥K => (y : G)) h1
  simp only [hα, normalizerMonoidHom_coe] at h2
  simpa using h2


theorem adjust_odd (hK : SL2SylowLeaf) [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂)
    (hs : GenSyl G z S K₁ K₂ t u) (hodd : Odd q) (h5 : 5 ≤ q) {v : G} (hv : v ∈ C1z z K₁)
    (hvodd : Odd (orderOf v))
    (hvQ : v ∈ normalizer (((S : Subgroup G) ⊓ (K₁ ⊔ K₂) : Subgroup G) : Set G)) :
    ∃ n ∈ K₁ ⊔ K₂, ∀ x ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂), (n * v) * x = x * (n * v) := by
  have hv₂ := C1_normalizer₂ hc hv
  have h1 := fun x => mem_normalizer_iff.mp hvQ x
  have hvR₁ : ∀ x, x ∈ (S : Subgroup G) ⊓ K₁ ↔ v * x * v⁻¹ ∈ (S : Subgroup G) ⊓ K₁ := by
    intro x
    have h2 := mem_normalizer_iff.mp hv.2 x
    constructor
    · rintro ⟨hxS, hxK⟩
      have hxQ : x ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂) := ⟨hxS, Subgroup.mem_sup_left hxK⟩
      exact ⟨((h1 x).mp hxQ).1, h2.mp hxK⟩
    · rintro ⟨hvS, hvK⟩
      have hvQ' : v * x * v⁻¹ ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂) := ⟨hvS, Subgroup.mem_sup_left hvK⟩
      exact ⟨((h1 x).mpr hvQ').1, h2.mpr hvK⟩
  have hvR₂ : ∀ x, x ∈ (S : Subgroup G) ⊓ K₂ ↔ v * x * v⁻¹ ∈ (S : Subgroup G) ⊓ K₂ := by
    intro x
    have h2 := mem_normalizer_iff.mp hv₂ x
    constructor
    · rintro ⟨hxS, hxK⟩
      have hxQ : x ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂) := ⟨hxS, Subgroup.mem_sup_right hxK⟩
      exact ⟨((h1 x).mp hxQ).1, h2.mp hxK⟩
    · rintro ⟨hvS, hvK⟩
      have hvQ' : v * x * v⁻¹ ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂) := ⟨hvS, Subgroup.mem_sup_right hvK⟩
      exact ⟨((h1 x).mpr hvQ').1, h2.mpr hvK⟩
  obtain ⟨g₁, hg₁, hg₁x⟩ := adjust_component hK hc.sl₁ hodd h5 (inf_le_right : (S : Subgroup G) ⊓ K₁ ≤ K₁)
    (card_Q₁ hc hs) hv.2 hvodd hvR₁
  obtain ⟨g₂, hg₂, hg₂x⟩ := adjust_component hK hc.sl₂ hodd h5 (inf_le_right : (S : Subgroup G) ⊓ K₂ ≤ K₂)
    (card_Q₂ hc hs) hv₂ hvodd hvR₂
  refine ⟨(g₁ * g₂)⁻¹, Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hg₁)
    (Subgroup.mem_sup_right hg₂)), ?_⟩
  have hcen₁ : (S : Subgroup G) ⊓ K₁ ≤ centralizer (({((g₁ * g₂)⁻¹ * v)} : Set G)) := by
    intro x hx
    refine mem_centralizer_singleton_iff.mpr ?_
    have hxv := hg₁x x hx
    have hcomm : g₂⁻¹ * x = x * g₂⁻¹ := (hc.comm x hx.2 _ (Subgroup.inv_mem _ hg₂)).symm
    have hvx : v * x = (g₁ * x * g₁⁻¹) * v := by
      calc v * x = (v * x * v⁻¹) * v := by group
        _ = (g₁ * x * g₁⁻¹) * v := by rw [hxv]
    calc x * ((g₁ * g₂)⁻¹ * v) = (x * g₂⁻¹) * g₁⁻¹ * v := by group
      _ = (g₂⁻¹ * x) * g₁⁻¹ * v := by rw [hcomm]
      _ = (g₁ * g₂)⁻¹ * (g₁ * x * g₁⁻¹) * v := by group
      _ = (g₁ * g₂)⁻¹ * (v * x) := by rw [hvx]; group
      _ = ((g₁ * g₂)⁻¹ * v) * x := by group
  have hcen₂ : (S : Subgroup G) ⊓ K₂ ≤ centralizer (({((g₁ * g₂)⁻¹ * v)} : Set G)) := by
    intro x hx
    refine mem_centralizer_singleton_iff.mpr ?_
    have hxv := hg₂x x hx
    have h12 : g₁⁻¹ * g₂ = g₂ * g₁⁻¹ := hc.comm _ (Subgroup.inv_mem _ hg₁) _ hg₂
    have h12' : g₁⁻¹ * g₂⁻¹ = g₂⁻¹ * g₁⁻¹ :=
      hc.comm _ (Subgroup.inv_mem _ hg₁) _ (Subgroup.inv_mem _ hg₂)
    have h1x : g₁⁻¹ * x = x * g₁⁻¹ := hc.comm _ (Subgroup.inv_mem _ hg₁) x hx.2
    have hvx : v * x = (g₂ * x * g₂⁻¹) * v := by
      calc v * x = (v * x * v⁻¹) * v := by group
        _ = (g₂ * x * g₂⁻¹) * v := by rw [hxv]
    calc x * ((g₁ * g₂)⁻¹ * v) = x * (g₂⁻¹ * g₁⁻¹) * v := by group
      _ = x * (g₁⁻¹ * g₂⁻¹) * v := by rw [h12']
      _ = (x * g₁⁻¹) * g₂⁻¹ * v := by group
      _ = (g₁⁻¹ * x) * g₂⁻¹ * v := by rw [h1x]
      _ = g₂⁻¹ * (g₁⁻¹ * g₂) * x * g₂⁻¹ * v := by
          rw [h12]; group
      _ = (g₁ * g₂)⁻¹ * (g₂ * x * g₂⁻¹) * v := by group
      _ = (g₁ * g₂)⁻¹ * (v * x) := by rw [hvx]; group
      _ = ((g₁ * g₂)⁻¹ * v) * x := by group
  intro x hx
  rw [Q_eq_sup hc hs] at hx
  have hsup : (S : Subgroup G) ⊓ K₁ ⊔ (S : Subgroup G) ⊓ K₂ ≤
      centralizer (({((g₁ * g₂)⁻¹ * v)} : Set G)) := sup_le hcen₁ hcen₂
  exact (mem_centralizer_singleton_iff.mp (hsup hx)).symm


theorem pow_mul_mem_Nz (hc : LUComps G q z K₁ K₂) {n v : G} (hn : n ∈ Nz z K₁ K₂) (hv : v ∈ Cz z)
    (k : ℕ) : ∃ m ∈ Nz z K₁ K₂, (n * v) ^ k = m * v ^ k := by
  induction k with
  | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | succ k ih =>
    obtain ⟨m, hm, e⟩ := ih
    refine ⟨m * (v ^ k * n * (v ^ k)⁻¹),
      Subgroup.mul_mem _ hm (Nz_conj hc (Subgroup.pow_mem _ hv k) hn), ?_⟩
    rw [pow_succ, e, pow_succ]; group

theorem cent_sylow_mem_center (hK : SL2SylowLeaf) {K : Subgroup G} {q : ℕ}
    (hmod : HasSL2Model ↥K (fun r => r = q)) (hodd : Odd q) (h5 : 5 ≤ q)
    {R : Subgroup G} (hRK : R ≤ K) (hR : Nat.card ↥R = 2 ^ (Nat.card ↥K).factorization 2)
    {k : G} (hk : k ∈ K) (hkR : ∀ x ∈ R, k * x = x * k) :
    k ∈ (center ↥K).map K.subtype := by
  have hcard : Nat.card ↥(R.subgroupOf K) = 2 ^ (Nat.card ↥K).factorization 2 := by
    rw [← hR]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv
  have := ((hK ↥K q hmod hodd h5 (R.subgroupOf K) hcard).1) ⟨k, hk⟩ (fun y hy => by
    have hyR : (y : G) ∈ R := hy
    exact Subtype.ext (hkR y hyR))
  exact ⟨⟨k, hk⟩, this, rfl⟩

theorem Nz_cent_Q (hK : SL2SylowLeaf) [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂)
    (hs : GenSyl G z S K₁ K₂ t u) (hodd : Odd q) (h5 : 5 ≤ q) {n : G} (hn : n ∈ Nz z K₁ K₂)
    (hcQ : ∀ x ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂), n * x = x * n) :
    ∃ a ∈ A0 z, ∃ i : ℤ, n = a * z ^ i := by
  obtain ⟨a, ha, k, hk, rfl⟩ := mem_sup_of_commute (fun a ha k hk => A0_comm hc ha hk) hn
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := mem_sup_of_commute hc.comm hk
  have hQ₁ : ∀ x ∈ (S : Subgroup G) ⊓ K₁, k₁ * x = x * k₁ := by
    intro x hx
    have hxK : x ∈ K₁ ⊔ K₂ := Subgroup.mem_sup_left hx.2
    have e1 : a * (k₁ * k₂) * x = x * (a * (k₁ * k₂)) := hcQ x ⟨hx.1, hxK⟩
    have hax : a * x = x * a := A0_comm hc ha hxK
    have hk₂x : k₂ * x = x * k₂ := (hc.comm x hx.2 k₂ hk₂).symm
    have : a * (k₁ * x) * k₂ = a * (x * k₁) * k₂ := by
      calc a * (k₁ * x) * k₂ = a * k₁ * (x * k₂) := by group
        _ = a * k₁ * (k₂ * x) := by rw [hk₂x]
        _ = a * (k₁ * k₂) * x := by group
        _ = x * (a * (k₁ * k₂)) := e1
        _ = (x * a) * k₁ * k₂ := by group
        _ = (a * x) * k₁ * k₂ := by rw [hax]
        _ = a * (x * k₁) * k₂ := by group
    exact mul_left_cancel (mul_right_cancel this)
  have hQ₂ : ∀ x ∈ (S : Subgroup G) ⊓ K₂, k₂ * x = x * k₂ := by
    intro x hx
    have hxK : x ∈ K₁ ⊔ K₂ := Subgroup.mem_sup_right hx.2
    have e1 : a * (k₁ * k₂) * x = x * (a * (k₁ * k₂)) := hcQ x ⟨hx.1, hxK⟩
    have hax : a * x = x * a := A0_comm hc ha hxK
    have hk₁x : x * k₁ = k₁ * x := (hc.comm k₁ hk₁ x hx.2).symm
    have : a * k₁ * (k₂ * x) = a * k₁ * (x * k₂) := by
      calc a * k₁ * (k₂ * x) = a * (k₁ * k₂) * x := by group
        _ = x * (a * (k₁ * k₂)) := e1
        _ = (x * a) * (k₁ * k₂) := by group
        _ = (a * x) * (k₁ * k₂) := by rw [hax]
        _ = a * (x * k₁) * k₂ := by group
        _ = a * (k₁ * x) * k₂ := by rw [hk₁x]
        _ = a * k₁ * (x * k₂) := by group
    exact mul_left_cancel this
  have hz₁ := cent_sylow_mem_center hK hc.sl₁ hodd h5
    (inf_le_right : (S : Subgroup G) ⊓ K₁ ≤ K₁) (card_Q₁ hc hs) hk₁ hQ₁
  have hz₂ := cent_sylow_mem_center hK hc.sl₂ hodd h5
    (inf_le_right : (S : Subgroup G) ⊓ K₂ ≤ K₂) (card_Q₂ hc hs) hk₂ hQ₂
  rw [hc.cen₁] at hz₁
  rw [hc.cen₂] at hz₂
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hz₁
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hz₂
  exact ⟨a, ha, i + j, by rw [zpow_add]⟩


theorem Nz_le_C1z [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂) : Nz z K₁ K₂ ≤ C1z z K₁ := by
  refine sup_le (le_inf A0_le_Cz ?_) (le_inf (K_le_Cz hc) hc.le_normalizer₁)
  intro a ha
  refine Subgroup.centralizer_le_normalizer (K₁ : Set G) ?_
  refine mem_centralizer_iff.mpr ?_
  intro h hh
  exact A0_comm hc ha (Subgroup.mem_sup_left hh) |>.symm

omit [Finite G] in
theorem exists_orderOf_pow_of_pow_eq_one {x : G} {k : ℕ} (h : x ^ (2 ^ k) = 1) :
    ∃ j : ℕ, orderOf x = 2 ^ j := by
  have := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp this
  exact ⟨j, hj⟩

theorem gen_decomp (hK : SL2SylowLeaf) [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂)
    (hs : GenSyl G z S K₁ K₂ t u) (hodd : Odd q) (h5 : 5 ≤ q) {c : G} (hc1 : c ∈ C1z z K₁) :
    ∃ n ∈ Nz z K₁ K₂, ∃ s ∈ (S : Subgroup G) ⊓ C1z z K₁, ∃ y ∈ C1z z K₁,
      c = n * s * y ∧ Odd (orderOf y) ∧
        ∀ x ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂), x * y = y * x := by
  obtain ⟨n₁, hn₁, hv⟩ := frattini_Q hc hs hc1.1
  set v := n₁⁻¹ * c with hvdef
  have hn₁C1 : n₁ ∈ C1z z K₁ := Nz_le_C1z hc hn₁
  have hvC1 : v ∈ C1z z K₁ := Subgroup.mul_mem _ (Subgroup.inv_mem _ hn₁C1) hc1
  obtain ⟨a, b, hab, ⟨k, hk⟩, ⟨m, hm, hbm⟩⟩ := exists_split_two v
  have hv₂C1 : v ^ a ∈ C1z z K₁ := Subgroup.zpow_mem _ hvC1 a
  have hv₀C1 : v ^ b ∈ C1z z K₁ := Subgroup.zpow_mem _ hvC1 b
  obtain ⟨j, hj⟩ := exists_orderOf_pow_of_pow_eq_one hk
  obtain ⟨n₂, hn₂, s, hs', hv₂eq⟩ := two_elt_mem_N_S1 hc hs hodd h5 hv₂C1 hj
  have hv₀odd : Odd (orderOf (v ^ b)) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hbm)
  have hv₀Q : v ^ b ∈ normalizer (((S : Subgroup G) ⊓ (K₁ ⊔ K₂) : Subgroup G) : Set G) :=
    Subgroup.zpow_mem _ hv b
  obtain ⟨n₃, hn₃K, hn₃⟩ := adjust_odd hK hc hs hodd h5 hv₀C1 hv₀odd hv₀Q
  have hn₃N : n₃ ∈ Nz z K₁ K₂ := Subgroup.mem_sup_right hn₃K
  have hn₃C1 : n₃ ∈ C1z z K₁ := Nz_le_C1z hc hn₃N
  set y₁ := n₃ * v ^ b with hy₁
  have hy₁C1 : y₁ ∈ C1z z K₁ := Subgroup.mul_mem _ hn₃C1 hv₀C1
  have hy₁r : y₁ ^ (orderOf (v ^ b)) ∈ Nz z K₁ K₂ := by
    obtain ⟨m', hm', e⟩ := pow_mul_mem_Nz hc hn₃N hv₀C1.1 (orderOf (v ^ b))
    rw [hy₁, e, pow_orderOf_eq_one, mul_one]
    exact hm'
  obtain ⟨a', b', hab', ⟨k', hk'⟩, ⟨m', hm', hbm'⟩⟩ := exists_split_two y₁
  have hy₁₂ord := exists_orderOf_pow_of_pow_eq_one hk'
  obtain ⟨j', hj'⟩ := hy₁₂ord
  have hy₁₂N : y₁ ^ a' ∈ Nz z K₁ K₂ := by
    have h1 : (y₁ ^ a') ^ (orderOf (v ^ b)) ∈ Nz z K₁ K₂ := by
      have : (y₁ ^ a') ^ (orderOf (v ^ b)) = (y₁ ^ (orderOf (v ^ b))) ^ a' := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
      rw [this]
      exact Subgroup.zpow_mem _ hy₁r a'
    have hcop : (orderOf (v ^ b)).gcd (orderOf (y₁ ^ a')) = 1 := by
      rw [hj']
      exact Nat.Coprime.pow_right j' (Nat.coprime_two_right.mpr hv₀odd)
    have h2 : y₁ ^ a' ∈ zpowers ((y₁ ^ a') ^ (orderOf (v ^ b))) := mem_zpowers_pow_iff.mpr hcop
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h2
    rw [← hi]
    exact Subgroup.zpow_mem _ h1 i
  have hyC1 : y₁ ^ b' ∈ C1z z K₁ := Subgroup.zpow_mem _ hy₁C1 b'
  have hyodd : Odd (orderOf (y₁ ^ b')) := Odd.of_dvd_nat hm' (orderOf_dvd_of_pow_eq_one hbm')
  have hyQ : ∀ x ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂), x * y₁ ^ b' = y₁ ^ b' * x := by
    intro x hx
    have h1 : x * y₁ = y₁ * x := (hn₃ x hx).symm
    exact (Commute.zpow_right (show Commute x y₁ from h1) b')
  have hsC1 : s ∈ C1z z K₁ := hs'.2
  have hsN : ∀ n ∈ Nz z K₁ K₂, s * n * s⁻¹ ∈ Nz z K₁ K₂ := fun n hn => Nz_conj hc hsC1.1 hn
  refine ⟨n₁ * n₂ * (s * (n₃⁻¹ * y₁ ^ a') * s⁻¹), ?_, s, hs', y₁ ^ b', hyC1, ?_, hyodd, hyQ⟩
  · refine Subgroup.mul_mem _ (Subgroup.mul_mem _ hn₁ hn₂) (hsN _ ?_)
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hn₃N) hy₁₂N
  ·
    have e1 : c = n₁ * v := by rw [hvdef]; group
    have e2 : v = v ^ a * v ^ b := hab.symm
    have e3 : y₁ = y₁ ^ a' * y₁ ^ b' := hab'.symm
    have e4 : v ^ b = n₃⁻¹ * y₁ := by rw [hy₁]; group
    calc c = n₁ * (v ^ a * v ^ b) := by rw [e1, ← e2]
      _ = n₁ * (n₂ * s) * (v ^ b) := by rw [← hv₂eq]; group
      _ = n₁ * (n₂ * s) * (n₃⁻¹ * (y₁ ^ a' * y₁ ^ b')) := by rw [e4, ← e3]
      _ = n₁ * n₂ * (s * (n₃⁻¹ * y₁ ^ a') * s⁻¹) * s * y₁ ^ b' := by group


omit [Finite G] in
theorem u_mem_C1z (hs : GenSyl G z S K₁ K₂ t u) : u ∈ C1z z K₁ := ⟨hs.S_le_Cz hs.u_mem, hs.u_norm⟩

omit [Finite G] in
theorem zpow_z_eq (hz2 : z * z = 1) (i : ℤ) (m : ℕ) (hm : Odd m) : z ^ (i * m) = z ^ i := by
  obtain ⟨k, rfl⟩ := hm
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz2
  have : i * ((2 * k + 1 : ℕ) : ℤ) = (2 : ℤ) * (i * k) + i := by push_cast; ring
  rw [this, zpow_add, zpow_mul, h2, one_zpow, one_mul]

theorem y_comm_u (hK : SL2SylowLeaf) [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂)
    (hs : GenSyl G z S K₁ K₂ t u) (hodd : Odd q) (h5 : 5 ≤ q)
    (hu : ∀ a ∈ A0 z, u * a * u⁻¹ = a) {y : G} (hy : y ∈ C1z z K₁) (hyodd : Odd (orderOf y))
    (hyQ : ∀ x ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂), x * y = y * x) : u * y = y * u := by
  set c := u * y * u⁻¹ * y⁻¹ with hcdef
  have huC1 : u ∈ C1z z K₁ := u_mem_C1z hs
  have hcN : c ∈ Nz z K₁ K₂ := commutator_mem_Nz hc hs hodd h5 huC1 hy
  have hcQ : ∀ x ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂), c * x = x * c := by
    intro x hx
    have hx' : u⁻¹ * x * u ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂) := by
      refine ⟨?_, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hs.u_mem) hx.1) hs.u_mem
      · have := hc.conj_sup_mem (Subgroup.inv_mem _ (hs.S_le_Cz hs.u_mem)) hx.2
        simpa using this
    have h1 : (u⁻¹ * x * u) * y = y * (u⁻¹ * x * u) := hyQ _ hx'
    have h2 : y⁻¹ * x = x * y⁻¹ := by
      have := hyQ x hx
      calc y⁻¹ * x = y⁻¹ * (x * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * x) * y⁻¹ := by rw [this]
        _ = x * y⁻¹ := by group
    calc c * x = u * y * u⁻¹ * (y⁻¹ * x) := by rw [hcdef]; group
      _ = u * y * u⁻¹ * (x * y⁻¹) := by rw [h2]
      _ = u * (y * (u⁻¹ * x * u)) * u⁻¹ * y⁻¹ := by group
      _ = u * ((u⁻¹ * x * u) * y) * u⁻¹ * y⁻¹ := by rw [h1]
      _ = (u * (u⁻¹ * x * u) * u⁻¹) * (u * y * u⁻¹ * y⁻¹) := by group
      _ = x * c := by rw [hcdef]; group
  obtain ⟨a, ha, i, hai⟩ := Nz_cent_Q hK hc hs hodd h5 hcN hcQ
  have hz2 := hs.z_sq
  have huz : u * z = z * u := hs.comm_z u hs.u_mem
  have huzi : u * z ^ i * u⁻¹ = z ^ i := by
    have : Commute u z := huz
    have h := (this.zpow_right i).eq
    calc u * z ^ i * u⁻¹ = z ^ i * u * u⁻¹ := by rw [← h]
      _ = z ^ i := by group
  have huc : u * c * u⁻¹ = c := by
    rw [hai, show u * (a * z ^ i) * u⁻¹ = (u * a * u⁻¹) * (u * z ^ i * u⁻¹) by group, hu a ha, huzi]
  have hcy : u * y * u⁻¹ = c * y := by rw [hcdef]; group
  have hcc : c * c = 1 := by
    have h1 : u * (u * y * u⁻¹) * u⁻¹ = y := by
      have : u * u = 1 := hs.u_sq
      calc u * (u * y * u⁻¹) * u⁻¹ = (u * u) * y * (u * u)⁻¹ := by group
        _ = y := by rw [this]; group
    rw [hcy] at h1
    have h2 : u * (c * y) * u⁻¹ = c * (c * y) := by
      calc u * (c * y) * u⁻¹ = (u * c * u⁻¹) * (u * y * u⁻¹) := by group
        _ = c * (c * y) := by rw [huc, hcy]
    rw [h2] at h1
    have : (c * c) * y = 1 * y := by rw [mul_assoc, h1, one_mul]
    exact mul_right_cancel this
  have hAz : a * z = z * a := mem_centralizer_singleton_iff.mp (A0_le_Cz ha)
  have hcomm_az : Commute a (z ^ i) := (show Commute a z from hAz).zpow_right i
  have ha1 : a = 1 := by
    have h1 : (a * z ^ i) * (a * z ^ i) = a * a := by
      have hzz : z ^ i * z ^ i = 1 := by
        rw [← zpow_add, ← two_mul, zpow_mul, show z ^ (2 : ℤ) = 1 by rw [zpow_two]; exact hz2, one_zpow]
      calc (a * z ^ i) * (a * z ^ i) = a * (z ^ i * a) * z ^ i := by group
        _ = a * (a * z ^ i) * z ^ i := by rw [← hcomm_az.eq]
        _ = a * a * (z ^ i * z ^ i) := by group
        _ = a * a := by rw [hzz, mul_one]
    rw [hai] at hcc
    rw [h1] at hcc
    have hord : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hcc)
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (h ▸ odd_orderOf_A0 ha) (by decide)
  have hczi : c = z ^ i := by rw [hai, ha1, one_mul]
  have hyz : y * z = z * y := mem_centralizer_singleton_iff.mp hy.1
  have hcyc : Commute c y := by
    rw [hczi]; exact ((show Commute z y from hyz.symm).zpow_left i)
  have hm : y ^ (orderOf y) = 1 := pow_orderOf_eq_one y
  have h3 : (u * y * u⁻¹) ^ (orderOf y) = 1 := by
    rw [conj_pow, hm]; group
  rw [hcy, hcyc.mul_pow, hm, mul_one] at h3
  have hz1 : z ^ i = 1 := by
    rw [hczi, ← zpow_natCast, ← zpow_mul, zpow_z_eq hz2 i (orderOf y) hyodd] at h3
    exact h3
  have hc1 : c = 1 := by rw [hczi, hz1]
  rw [hc1, one_mul] at hcy
  calc u * y = (u * y * u⁻¹) * u := by group
    _ = y * u := by rw [hcy]


theorem Q₁_not_le_zpowers [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂)
    (hs : GenSyl G z S K₁ K₂ t u) : ¬ ((S : Subgroup G) ⊓ K₁ ≤ zpowers z) := by
  intro hle
  have hzQ : zpowers z ≤ (S : Subgroup G) ⊓ K₁ := by
    rw [zpowers_le]; exact ⟨hs.z_mem, hc.z_mem₁⟩
  have heq : (S : Subgroup G) ⊓ K₁ = zpowers z := le_antisymm hle hzQ
  have hc2 := card_Q₁ hc hs
  rw [heq, Nat.card_zpowers, hs.z_inv] at hc2
  have hv : (Nat.card ↥K₁).factorization 2 = 1 := by
    have h2 : (2 : ℕ) ^ 1 = 2 ^ (Nat.card ↥K₁).factorization 2 := by simpa using hc2
    exact (Nat.pow_right_injective le_rfl h2).symm
  obtain ⟨O, -, hO⟩ := exists_index_two_of_card_two_sylow (D := ↥K₁) hv
  have hcard : Nat.card ↥(O.map K₁.subtype) * 2 = Nat.card ↥K₁ := by
    rw [Subgroup.card_map_of_injective K₁.subtype_injective, ← hO]
    exact Subgroup.card_mul_index O
  exact perfect_no_index_two hc.perfect₁ (Subgroup.map_subtype_le O) hcard

theorem normalizer_of_cent_Q [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂)
    (hs : GenSyl G z S K₁ K₂ t u) {h : G} (hz : h ∈ Cz z)
    (hh : ∀ x ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂), h * x = x * h) : h ∈ normalizer (K₁ : Set G) := by
  by_contra hn
  obtain ⟨e1, -⟩ := hc.swap_of_not_normalizer hz hn
  obtain ⟨x, hxQ, hxz⟩ := (IsConcreteLE.not_le_iff_exists).mp (Q₁_not_le_zpowers hc hs)
  have hxQ' : x ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂) := ⟨hxQ.1, Subgroup.mem_sup_left hxQ.2⟩
  have h1 : h * x * h⁻¹ = x := by rw [hh x hxQ']; group
  have h2 : h * x * h⁻¹ ∈ K₂ := LUComps.mem_of_map e1 hxQ.2
  rw [h1] at h2
  apply hxz
  rw [← hc.inf_eq]
  exact ⟨hxQ.2, h2⟩

theorem y_mem_Fstar (hK : SL2SylowLeaf) [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂)
    (hs : GenSyl G z S K₁ K₂ t u) (hodd : Odd q) (h5 : 5 ≤ q)
    (hu : ∀ a ∈ A0 z, u * a * u⁻¹ = a) {y : G} (hy : y ∈ C1z z K₁) (hyodd : Odd (orderOf y))
    (hyQ : ∀ x ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂), x * y = y * x) (hyu : u * y = y * u) :
    y ∈ Fstar (S : Subgroup G) K₁ K₂ u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := (S : Subgroup G) ⊓ (K₁ ⊔ K₂) ⊔ zpowers u with hP
  set H : Subgroup G := centralizer (P : Set G) with hH
  have hQP : (S : Subgroup G) ⊓ (K₁ ⊔ K₂) ≤ P := le_sup_left
  have huP : u ∈ P := Subgroup.mem_sup_right (mem_zpowers u)
  have hzQ : z ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂) := ⟨hs.z_mem, Subgroup.mem_sup_left hc.z_mem₁⟩
  have hHcen : ∀ h ∈ H, ∀ p ∈ P, p * h = h * p := fun h hh p hp => mem_centralizer_iff.mp hh p hp
  have hHC1 : H ≤ C1z z K₁ := by
    intro h hh
    have hz : h ∈ Cz z := mem_centralizer_singleton_iff.mpr (hHcen h hh z (hQP hzQ)).symm
    exact ⟨hz, normalizer_of_cent_Q hc hs hz (fun x hx => (hHcen h hh x (hQP hx)).symm)⟩
  have hyH : y ∈ H := by
    refine mem_centralizer_iff.mpr (fun p hp => ?_)
    have hle : P ≤ centralizer ({y} : Set G) := by
      refine sup_le (fun x hx => mem_centralizer_singleton_iff.mpr (hyQ x hx)) ?_
      rw [zpowers_le]
      exact mem_centralizer_singleton_iff.mpr hyu
    exact mem_centralizer_singleton_iff.mp (hle hp)
  have hA0H : A0 z ≤ H := by
    intro a ha
    refine mem_centralizer_iff.mpr (fun p hp => ?_)
    have hle : P ≤ centralizer ({a} : Set G) := by
      refine sup_le (fun x hx => mem_centralizer_singleton_iff.mpr ?_) ?_
      · exact (A0_comm hc ha hx.2).symm
      · rw [zpowers_le]
        refine mem_centralizer_singleton_iff.mpr ?_
        have := hu a ha
        calc u * a = (u * a * u⁻¹) * u := by group
          _ = a * u := by rw [this]
    exact mem_centralizer_singleton_iff.mp (hle hp)
  set O₁ : Subgroup G := A0 z ⊔ zpowers y with hO₁
  have hO₁H : O₁ ≤ H := sup_le hA0H (by rw [zpowers_le]; exact hyH)
  have hO₁odd : Odd (Nat.card ↥O₁) := by
    refine odd_card_sup_of_le_normalizer ?_ ?_ ?_
    · rw [zpowers_le]; exact mem_normalizer_pPrimeCoreOf hy.1
    · exact Nat.coprime_two_left.mp (coprime_card_A0 z)
    · rw [Nat.card_zpowers]; exact hyodd
  have hz2 := hs.z_sq
  have hconj : ∀ h ∈ H, h * y * h⁻¹ ∈ O₁ := by
    intro h hh
    have hhC1 : h ∈ C1z z K₁ := hHC1 hh
    have hcN := commutator_mem_Nz hc hs hodd h5 hhC1 hy
    have hcQ : ∀ x ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂),
        (h * y * h⁻¹ * y⁻¹) * x = x * (h * y * h⁻¹ * y⁻¹) := by
      intro x hx
      have hxh : Commute x h := hHcen h hh x (hQP hx)
      have hxy : Commute x y := hyQ x hx
      exact (((hxh.mul_right hxy).mul_right hxh.inv_right).mul_right hxy.inv_right).eq.symm
    obtain ⟨a, ha, i, hai⟩ := Nz_cent_Q hK hc hs hodd h5 hcN hcQ
    have hwO : a * y ∈ O₁ :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (mem_zpowers y))
    have hzy : Commute z y := (mem_centralizer_singleton_iff.mp hy.1).symm
    have hza : Commute z a := (mem_centralizer_singleton_iff.mp (A0_le_Cz ha)).symm
    have hzw : Commute (z ^ i) (a * y) := (hza.zpow_left i).mul_right (hzy.zpow_left i)
    have hconjeq : h * y * h⁻¹ = z ^ i * (a * y) := by
      calc h * y * h⁻¹ = (h * y * h⁻¹ * y⁻¹) * y := by group
        _ = (a * z ^ i) * y := by rw [hai]
        _ = (z ^ i * a) * y := by rw [← (hza.zpow_left i).eq]
        _ = z ^ i * (a * y) := by group
    have hodd_w : Odd (orderOf (a * y)) :=
      Odd.of_dvd_nat hO₁odd (Subgroup.orderOf_dvd_natCard O₁ hwO)
    have hord_conj : orderOf (h * y * h⁻¹) = orderOf y := by
      have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective y
      simpa [MulAut.conj_apply] using this
    have hz1 : z ^ i = 1 := by
      have e1 : (z ^ i * (a * y)) ^ (orderOf (a * y)) = z ^ i := by
        rw [hzw.mul_pow, pow_orderOf_eq_one, mul_one, ← zpow_natCast, ← zpow_mul,
          zpow_z_eq hz2 i (orderOf (a * y)) hodd_w]
      have h1 := orderOf_pow_dvd (x := z ^ i * (a * y)) (orderOf (a * y))
      rw [e1, ← hconjeq, hord_conj] at h1
      have h2 : Odd (orderOf (z ^ i)) := Odd.of_dvd_nat hyodd h1
      have hzz : z ^ i * z ^ i = 1 := by
        rw [← zpow_add, ← two_mul, zpow_mul, show z ^ (2 : ℤ) = 1 by rw [zpow_two]; exact hz2,
          one_zpow]
      have h3 : orderOf (z ^ i) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hzz)
      rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h4 | h4
      · exact orderOf_eq_one_iff.mp h4
      · exact absurd (h4 ▸ h2) (by decide)
    rw [hconjeq, hz1, one_mul]
    exact hwO
  have hy' : (⟨y, hyH⟩ : ↥H) ∈ (O₁.subgroupOf H).normalCore := by
    intro b
    rw [Subgroup.mem_subgroupOf]
    simpa using hconj (b : G) b.2
  have hcop : Nat.Coprime 2 (Nat.card ↥(O₁.subgroupOf H).normalCore) := by
    have hd : Nat.card ↥(O₁.subgroupOf H).normalCore ∣ Nat.card ↥(O₁.subgroupOf H) :=
      Subgroup.card_dvd_of_le (Subgroup.normalCore_le _)
    have hc2 : Nat.card ↥(O₁.subgroupOf H) = Nat.card ↥O₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO₁H).toEquiv
    rw [hc2] at hd
    exact Nat.coprime_two_left.mpr (Odd.of_dvd_nat hO₁odd hd)
  have hle : (O₁.subgroupOf H).normalCore ≤ pPrimeCore 2 ↥H := le_sSup ⟨inferInstance, hcop⟩
  exact ⟨⟨y, hyH⟩, hle hy', rfl⟩


theorem lu_gen_of_sl2 (hK : SL2SylowLeaf) [IsCyclic ↥(A0 z)] (hc : LUComps G q z K₁ K₂)
    (hs : GenSyl G z S K₁ K₂ t u) (hodd : Odd q) (h5 : 5 ≤ q)
    (hu : ∀ a ∈ A0 z, u * a * u⁻¹ = a) :
    ∀ c ∈ Cz z, ∃ a ∈ A0 z, ∃ k ∈ K₁ ⊔ K₂, ∃ s ∈ (S : Subgroup G),
      ∃ y ∈ Fstar (S : Subgroup G) K₁ K₂ u, c = a * k * s * y := by
  have key : ∀ c' ∈ C1z z K₁, ∃ a ∈ A0 z, ∃ k ∈ K₁ ⊔ K₂, ∃ s ∈ (S : Subgroup G),
      ∃ y ∈ Fstar (S : Subgroup G) K₁ K₂ u, c' = a * k * s * y := by
    intro c' hc'
    obtain ⟨n, hn, s, hs', y, hy, rfl, hyodd, hyQ⟩ := gen_decomp hK hc hs hodd h5 hc'
    have hyu := y_comm_u hK hc hs hodd h5 hu hy hyodd hyQ
    have hyF := y_mem_Fstar hK hc hs hodd h5 hu hy hyodd hyQ hyu
    obtain ⟨a, ha, k, hk, rfl⟩ := mem_sup_of_commute (fun a ha k hk => A0_comm hc ha hk) hn
    exact ⟨a, ha, k, hk, s, hs'.1, y, hyF, rfl⟩
  intro c hcz
  by_cases hn : c ∈ normalizer (K₁ : Set G)
  · exact key c ⟨hcz, hn⟩
  · obtain ⟨e1, -⟩ := hc.swap_of_not_normalizer hcz hn
    have htC : t ∈ Cz z := hs.S_le_Cz hs.t_mem
    have ht1 : t⁻¹ * c ∈ C1z z K₁ := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ htC) hcz, ?_⟩
      refine mem_normalizer_iff.mpr (fun x => ?_)
      have h1 : ∀ y, y ∈ K₂ ↔ c⁻¹ * y * c ∈ K₁ := by
        intro y; rw [← e1, mem_map_conj_iff]
      have h2 : ∀ y, y ∈ K₂ ↔ t⁻¹ * y * t ∈ K₁ := by
        intro y; rw [← hs.t_swap, mem_map_conj_iff]
      calc x ∈ K₁ ↔ c * x * c⁻¹ ∈ K₂ := by
            rw [h1 (c * x * c⁻¹)]
            have : c⁻¹ * (c * x * c⁻¹) * c = x := by group
            rw [this]
        _ ↔ t⁻¹ * (c * x * c⁻¹) * t ∈ K₁ := h2 _
        _ ↔ (t⁻¹ * c) * x * (t⁻¹ * c)⁻¹ ∈ K₁ := by
            have : t⁻¹ * (c * x * c⁻¹) * t = (t⁻¹ * c) * x * (t⁻¹ * c)⁻¹ := by group
            rw [this]
    obtain ⟨a, ha, k, hk, s, hsS, y, hyF, he⟩ := key _ ht1
    refine ⟨t * a * t⁻¹, A0_conj htC ha, t * k * t⁻¹, hc.conj_sup_mem htC hk, t * s,
      (S : Subgroup G).mul_mem hs.t_mem hsS, y, hyF, ?_⟩
    have : c = t * (t⁻¹ * c) := by group
    rw [this, he]
    group

end CFSG.GH74.GLS.LU.Local
