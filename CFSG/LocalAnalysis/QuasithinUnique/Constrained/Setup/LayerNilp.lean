module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilpF
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilpA

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem NaturalS3Factors.of_comm_eq {G N N' A : Subgroup (V ≃ₗ[k] V)} {ι : Type*}
    {g : ι → V ≃ₗ[k] V} (h : NaturalS3Factors G N A g) (hL : ⁅N', A⁆ = ⁅N, A⁆)
    (hDle : natD N A g ≤ N')
    (hNeq : natD N A g ⊔ (N' ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (natW N A g)) = N')
    (hdisj : Disjoint (natD N A g) (N' ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (natW N A g)))
    (hC : N' ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (natW N A g) =
      N' ⊓ Subgroup.centralizer (natB G N A : Set (V ≃ₗ[k] V))) :
    NaturalS3Factors G N' A g := by
  have hLs : ∀ i, natL N' A g i = natL N A g i := fun i => by simp only [natL, hL]
  have hSs : ∀ i, natS N' A g i = natS N A g i := fun i => by simp only [natS, hLs]
  have hIs : ∀ i, natI N' A g i = natI N A g i := fun i => by simp only [natI, hLs]
  have hDs : natD N' A g = natD N A g := by simp only [natD, hLs]
  have hWs : natW N' A g = natW N A g := by simp only [natW, hDs]
  have hBs : natB G N' A = natB G N A := by simp only [natB, hL]
  exact
    { card_k := h.card_k
      card_L := fun i => by rw [hLs]; exact h.card_L i
      card_A := h.card_A
      finrank_I := fun i => by rw [hIs]; exact h.finrank_I i
      L_comm := fun i j hij => by rw [hLs, hLs]; exact h.L_comm i j hij
      L_indep := by
        have : natL N' A g = natL N A g := funext hLs
        rw [this]
        exact h.L_indep
      D_le_N := by rw [hDs]; exact hDle
      D_normal := by rw [hDs]; exact h.D_normal
      D_elem := by rw [hDs]; exact h.D_elem
      card_D := by rw [hDs]; exact h.card_D
      I_indep := by
        have : natI N' A g = natI N A g := funext hIs
        rw [this]
        exact h.I_indep
      W_eq := by
        have : natI N' A g = natI N A g := funext hIs
        rw [hWs, this]
        exact h.W_eq
      V_compl := by rw [hWs, hDs]; exact h.V_compl
      S_comm := fun i j hij => by rw [hSs, hSs]; exact h.S_comm i j hij
      S_indep := by
        have : natS N' A g = natS N A g := funext hSs
        rw [this]
        exact h.S_indep
      B_eq := by
        have : natS N' A g = natS N A g := funext hSs
        rw [hBs, this]
        exact h.B_eq
      B_le := by rw [hBs]; exact h.B_le
      B_normal := by rw [hBs]; exact h.B_normal
      LA_le_B := by rw [hL, hBs]; exact h.LA_le_B
      S_action := fun i => by
        rw [hSs, hIs]
        exact h.S_action i
      S_fix_I := fun i j hij => by rw [hSs, hIs]; exact h.S_fix_I i j hij
      S_fix_C := fun i => by rw [hDs, hSs]; exact h.S_fix_C i
      S_choice := fun x hx i hxi => by
        rw [hL, hLs] at hxi
        rw [hL, hSs]
        exact h.S_choice x hx i hxi
      S_perm := fun x hx i => by
        simp only [hSs, hLs, hIs]
        exact h.S_perm x hx i
      S_trans := fun i j => by
        simp only [hSs, hLs, hIs]
        exact h.S_trans i j
      B_derived := by rw [hBs, hDs]; exact h.B_derived
      S_le_B := fun i => by rw [hSs, hBs]; exact h.S_le_B i
      S_normal_B := fun i => by rw [hSs, hBs]; exact h.S_normal_B i
      N_eq := by rw [hDs, hWs]; exact hNeq
      N_disjoint := by rw [hDs, hWs]; exact hdisj
      C_eq := by rw [hWs, hBs]; exact hC }

structure NilpotentS3Factors (G Fn A : Subgroup (V ≃ₗ[k] V)) {ι : Type*}
    (g : ι → V ≃ₗ[k] V) : Prop where
  toNatural : NaturalS3Factors G Fn A g
  centralizes : ∀ f ∈ Fn, ∀ d ∈ natD Fn A g, f * d = d * f

theorem conjR_le_of_normal {G Fn L : Subgroup (V ≃ₗ[k] V)} (hFG : Fn ≤ G)
    (hFn : (Fn.subgroupOf G).Normal) (hL : L ≤ Fn) {x : V ≃ₗ[k] V} (hx : x ∈ G) :
    conjR x L ≤ Fn := by
  intro y hy
  rw [mem_conjR] at hy
  have hxn : x⁻¹ ∈ Subgroup.normalizer (Fn : Set (V ≃ₗ[k] V)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFG).1 hFn (G.inv_mem hx)
  have := hL hy
  have h2 := (Subgroup.mem_normalizer_iff.1 hxn (x * y * x⁻¹)).1 this
  simpa [mul_assoc] using h2

theorem ConjFamily.of_comm_eq {G N N' A : Subgroup (V ≃ₗ[k] V)} {ι : Type*}
    {g : ι → V ≃ₗ[k] V} (F : ConjFamily G N A g) (hL : ⁅N', A⁆ = ⁅N, A⁆) :
    ConjFamily G N' A g :=
  have e : natL N' A g = natL N A g := funext fun i => by simp only [natL, hL]
  ⟨F.mem, by rw [e]; exact F.inj, fun x hx => by rw [hL, e]; exact F.all x hx⟩

variable [CharP k 2] [Finite V]

theorem nilpotent_offender_natural_S3_factors {G Fn A : Subgroup (V ≃ₗ[k] V)} (hFG : Fn ≤ G)
    (hFn : (Fn.subgroupOf G).Normal) [Group.IsNilpotent ↥Fn] (hodd : Odd (Nat.card Fn))
    (hAG : A ≤ G) (hAel : CFSG.IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A)
    (hstrict : ∀ B : Subgroup (V ≃ₗ[k] V), ⊥ < B → B < A →
      weight (MonoidHom.id (V ≃ₗ[k] V)) B < weight (MonoidHom.id (V ≃ₗ[k] V)) A)
    (hcomm : ⁅Fn, A⁆ ≠ ⊥) :
    Nat.card k = 2 ∧ Nat.card A = 2 ∧
    (∃ C : Subgroup (V ≃ₗ[k] V), C ≤ Fn ∧ IsCyclic C ∧
      A ≤ Subgroup.normalizer (C : Set (V ≃ₗ[k] V)) ∧ ⁅C, A⁆ = ⁅Fn, A⁆) ∧
    Nat.card ↥(⁅Fn, A⁆ : Subgroup (V ≃ₗ[k] V)) = 3 ∧
    ((⁅Fn, A⁆ : Subgroup (V ≃ₗ[k] V)).subgroupOf G).IsSubnormal ∧
    commGL ⁅Fn, A⁆ ⊤ = commGL (⁅Fn, A⁆ ⊔ A) ⊤ ∧
    Module.finrank k ↥(commGL ⁅Fn, A⁆ ⊤) = 2 ∧
    (∃ hW : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (⁅Fn, A⁆ ⊔ A) (commGL ⁅Fn, A⁆ ⊤),
      Function.Bijective
        (resSub (MonoidHom.id (V ≃ₗ[k] V)) (⁅Fn, A⁆ ⊔ A) (commGL ⁅Fn, A⁆ ⊤) hW)) ∧
    commGL ⁅Fn, A⁆ ⊤ ⊔ fixGL A = ⊤ ∧
    weight (MonoidHom.id (V ≃ₗ[k] V)) A = Nat.card V ∧
    (∃ (ι : Type v) (_ : Fintype ι) (g : ι → V ≃ₗ[k] V), ConjFamily G Fn A g) ∧
    ∀ {ι : Type*} [Fintype ι] (g : ι → V ≃ₗ[k] V), ConjFamily G Fn A g →
      NilpotentS3Factors G Fn A g := by
  classical
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  obtain ⟨⟨C, hCF, hCcyc, hCA, hCcomm⟩, hsub⟩ :=
    exists_cyclic_invariant hFG hAG hFn hodd hAel hcomm
  have h0 : OddAbelianSetting (C ⊔ A) C A :=
    { N_le := le_sup_left
      N_normal := (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le (Subgroup.le_normalizer) hCA)
      N_abelian := fun x y => Subtype.ext (cyclic_comm hCcyc x x.2 y y.2)
      N_odd := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hCF)
      A_le := le_sup_right
      A_elem := hAel
      A_ne := hAne
      offender := hoff
      strict := hstrict
      comm_ne := hCcomm }
  obtain ⟨I, hT⟩ := h0.threePlane
  have hIeq := hT.I_eq
  subst hIeq
  have hk : Nat.card k = 2 := hT.card_k
  have hL3 : Nat.card ↥(⁅C, A⁆ : Subgroup (V ≃ₗ[k] V)) = 3 := hT.card_L
  have hLperf : ⁅⁅C, A⁆, A⁆ = ⁅C, A⁆ := h0.comm_comm
  have hLC : ⁅C, A⁆ ≤ C := h0.L_le_N
  have hLF : ⁅C, A⁆ ≤ Fn := hLC.trans hCF
  have hLG : ⁅C, A⁆ ≤ G := hLF.trans hFG
  have hI2 : Module.finrank k ↥(commGL ⁅C, A⁆ ⊤) = 2 := hT.finrank_I
  have hLsub : (⁅C, A⁆.subgroupOf G).IsSubnormal :=
    isSubnormal_trans (B := ⁅C, A⁆) (L := Fn) (K := G) hLF hFG (hsub _ hLF) hFn.isSubnormal
  obtain ⟨D, hLD, hDconj, hDset, hDL, hDeq⟩ :=
    exists_abelian_closure hLG hAG hk hL3 hI2 hLperf hLsub hAel hAne hoff hstrict
  have hDF : D ≤ Fn := by
    rw [hDeq]
    exact iSup₂_le fun x hx => conjR_le_of_normal hFG hFn hLF hx
  have hover : OverGroup G Fn D := ⟨hFG, hFn, hodd, hDF⟩
  obtain ⟨ι₀, hfin₀, g₀, F₀⟩ := exists_conjFamily G D A
  have hLeq : ⁅Fn, A⁆ = ⁅D, A⁆ := hDset.comm_Fn_eq F₀ hover
  have hcomm_eq : ⁅Fn, A⁆ = ⁅C, A⁆ := hLeq.trans hDL
  refine ⟨hk, hT.card_A, ⟨C, hCF, hCcyc, hCA, hcomm_eq.symm⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨ι₀, hfin₀, g₀, F₀.of_comm_eq hLeq⟩, ?_⟩
  · rw [hcomm_eq]; exact hL3
  · rw [hcomm_eq]; exact hLsub
  · rw [hcomm_eq]; exact hT.I_eq'
  · rw [hcomm_eq]; exact hI2
  · rw [hcomm_eq]; exact hT.action
  · rw [hcomm_eq]; exact hT.V_eq
  · exact hT.weight_eq
  · intro ι _ g Fg
    have Fg' : ConjFamily G D A g := Fg.of_comm_eq hLeq.symm
    have hS := hDset.naturalS3Factors Fg'
    have hnat : NaturalS3Factors G Fn A g :=
      hS.of_comm_eq hLeq (hDset.D_le_Fn Fg' hover) (hDset.N_eq_Fn Fg' hover)
        (hDset.N_disjoint_Fn Fg') (hDset.C_eq_Fn Fg' hover)
    refine ⟨hnat, fun f hf d hd => ?_⟩
    have hDs : natD Fn A g = natD D A g := by simp only [natD, natL, hLeq]
    rw [hDs] at hd
    exact hDset.centralizes_D Fg' hover hf d hd

end CFSG.QuasithinUnique.Setup.Layer
