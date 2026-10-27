module

public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem psimple_equiv_of_central_surj {Q F : Type} [Group Q] [Group F] (hQ : CFSG.Open.IsQuasisimple Q)
    (f : Q →* F) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center Q) [Nontrivial F] :
    Nonempty ((Q ⧸ Subgroup.center Q) ≃* (F ⧸ Subgroup.center F)) := by
  classical
  let φ : Q →* F ⧸ Subgroup.center F := (QuotientGroup.mk' (Subgroup.center F)).comp f
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hf
  have hcen : Subgroup.center Q ≤ φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' (Subgroup.center F) (f z) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro g
    obtain ⟨q, rfl⟩ := hf g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz q]
  have hker' : φ.ker = Subgroup.center Q := by
    refine le_antisymm ?_ hcen
    by_cases htop : φ.ker = ⊤
    ·
      exfalso
      have hcomm : ∀ q : Q, f q ∈ Subgroup.center F := by
        intro q
        have hq : q ∈ φ.ker := by rw [htop]; exact Subgroup.mem_top q
        rw [MonoidHom.mem_ker] at hq
        have h1 : QuotientGroup.mk' (Subgroup.center F) (f q) = 1 := hq
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact h1
      have hbot : ∀ a b : Q, ⁅a, b⁆ ∈ f.ker := by
        intro a b
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.1 (hcomm a) (f b)).symm
      have htopQ : (⊤ : Subgroup Q) ≤ f.ker := by
        have hc : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ f.ker :=
          Subgroup.commutator_le.2 fun a _ b _ => hbot a b
        have h2 : commutator Q = ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ := rfl
        rw [← h2, hQ.1] at hc
        exact hc
      obtain ⟨g, hg⟩ := exists_ne (1 : F)
      obtain ⟨q, rfl⟩ := hf g
      exact hg ((MonoidHom.mem_ker).1 (htopQ (Subgroup.mem_top q)))
    · exact le_center_of_normal_of_isQuasisimple hQ (inferInstance : φ.ker.Normal) htop
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker').symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs)⟩

theorem mem_glaPPrimeCoreOf_iff {G : Type} [Group G] {p : ℕ} {H : Subgroup G} (x : ↥H) :
    (x : G) ∈ GLAPPrimeCoreOf p H ↔ x ∈ GLAPPrimeCore p ↥H := by
  show (x : G) ∈ (GLAPPrimeCore p ↥H).map H.subtype ↔ _
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h
    have hxy : y = x := Subtype.ext hyx
    exact hxy ▸ hy
  · intro h
    exact Subgroup.mem_map.2 ⟨x, h, rfl⟩

theorem pSimple_equiv_of_comps {G : Type} [Group G] [Finite G] {p p' : ℕ} {X K : Subgroup G}
    (hp : p.Prime) (hp' : p'.Prime) (hK' : GLAPComponent p' X K) (hK : GLAPComponent p X K) :
    Nonempty (PSimple p' K ≃* PSimple p K) := by
  classical
  have hKX : K ≤ X := hK'.1
  have hsubK : IsSubnormal K X := hK'.2.1
  have hQ' : CFSG.Open.IsQuasisimple (PQuot p' K) := isQuasisimple_pQuot_of_glaPComponent hp' hK'
  have hQ : CFSG.Open.IsQuasisimple (PQuot p K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  set N : Subgroup ↥K := GLAPPrimeCore p' ↥K with hN
  set M : Subgroup ↥K := GLAPPrimeCore p ↥K with hM
  have hMne : M ≠ ⊤ := by
    intro hMt
    have hsub : Subsingleton (↥K ⧸ M) := by
      rw [hMt]
      exact QuotientGroup.subsingleton_quotient_top
    haveI := isQuasisimple_nontrivial hQ
    exact not_subsingleton (↥K ⧸ M) hsub
  have hPne : N ⊔ M ≠ ⊤ := by
    intro hP
    set J₀ : Subgroup G := M.map K.subtype with hJ₀
    have hJ₀le : J₀ ≤ K := Subgroup.map_subtype_le M
    have hsubMK : J₀.subgroupOf K = M := by
      ext x
      rw [Subgroup.mem_subgroupOf, hJ₀, Subgroup.mem_map]
      constructor
      · rintro ⟨m, hm, hmx⟩
        have hmx' : m = x := Subtype.ext hmx
        exact hmx' ▸ hm
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hJ₀ne : J₀ ≠ K := by
      intro hEq
      apply hMne
      rw [eq_top_iff]
      intro x _
      have hx : (x : G) ∈ J₀ := by
        rw [hEq]
        exact x.2
      obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 hx
      have hmx' : m = x := Subtype.ext hmx
      exact hmx' ▸ hm
    haveI : (J₀.subgroupOf K).Normal := by
      rw [hsubMK]
      infer_instance
    have hJ₀K : IsSubnormal J₀ K := IsSubnormal.step hJ₀le inferInstance (IsSubnormal.refl K)
    have hJ₀X : IsSubnormal J₀ X := isSubnormal_trans' hJ₀K hsubK
    have hNO : ∀ n : ↥K, n ∈ N → (⟨(n : G), hKX n.2⟩ : ↥X) ∈ GLAPPrimeCore p' ↥X := by
      intro n hn
      have h1 : (n : G) ∈ GLAPPrimeCoreOf p' K := (mem_glaPPrimeCoreOf_iff n).2 hn
      have h2 : (n : G) ∈ K ⊓ GLAPPrimeCoreOf p' X := by
        rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp' hsubK]
        exact h1
      exact (mem_glaPPrimeCoreOf_iff (⟨(n : G), hKX n.2⟩ : ↥X)).1 h2.2
    have hEq' : (J₀.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p' ↥X)) =
        (K.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p' ↥X)) := by
      apply le_antisymm
      · apply Subgroup.map_mono
        intro y hy
        rw [Subgroup.mem_subgroupOf] at hy ⊢
        exact hJ₀le hy
      · rintro _ ⟨x, hx, rfl⟩
        have hx' : (x : G) ∈ K := Subgroup.mem_subgroupOf.1 hx
        have hxK : (⟨(x : G), hx'⟩ : ↥K) ∈ N ⊔ M := by
          rw [hP]
          exact Subgroup.mem_top _
        rw [Subgroup.mem_sup_of_normal_right] at hxK
        obtain ⟨n, hn, m, hm, hnm⟩ := hxK
        have hmJ : (m : G) ∈ J₀ := Subgroup.mem_map.2 ⟨m, hm, rfl⟩
        have hnO : (⟨(n : G), hKX n.2⟩ : ↥X) ∈ GLAPPrimeCore p' ↥X := hNO n hn
        have h1 : QuotientGroup.mk' (GLAPPrimeCore p' ↥X) (⟨(n : G), hKX n.2⟩ : ↥X) = 1 :=
          (QuotientGroup.eq_one_iff _).2 hnO
        have hxeq : x = (⟨(n : G), hKX n.2⟩ : ↥X) * ⟨(m : G), hKX m.2⟩ := by
          apply Subtype.ext
          have hv := congrArg Subtype.val hnm
          simp only [Subgroup.coe_mul] at hv
          exact hv.symm
        refine Subgroup.mem_map.2 ⟨⟨(m : G), hKX m.2⟩, Subgroup.mem_subgroupOf.2 hmJ, ?_⟩
        rw [hxeq, map_mul, h1, one_mul]
    exact hK'.2.2.2 J₀ (lt_of_le_of_ne hJ₀le hJ₀ne) hJ₀X hEq'
  set P : Subgroup ↥K := N ⊔ M with hPdef
  haveI : Nontrivial (↥K ⧸ P) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    apply hPne
    rw [eq_top_iff]
    intro x _
    have h1 : (QuotientGroup.mk' P x : ↥K ⧸ P) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff x).1 h1
  have hPNne : P.map (QuotientGroup.mk' N) ≠ ⊤ := by
    intro h
    apply hPne
    rw [eq_top_iff]
    intro x _
    have hx : (QuotientGroup.mk' N x : ↥K ⧸ N) ∈ P.map (QuotientGroup.mk' N) := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.1 hx
    have h2 : k⁻¹ * x ∈ N := QuotientGroup.eq.1 hkx
    have hxk : x = k * (k⁻¹ * x) := by group
    rw [hxk]
    exact Subgroup.mul_mem _ hk (Subgroup.mem_sup_left h2)
  have hPMne : P.map (QuotientGroup.mk' M) ≠ ⊤ := by
    intro h
    apply hPne
    rw [eq_top_iff]
    intro x _
    have hx : (QuotientGroup.mk' M x : ↥K ⧸ M) ∈ P.map (QuotientGroup.mk' M) := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.1 hx
    have h2 : k⁻¹ * x ∈ M := QuotientGroup.eq.1 hkx
    have hxk : x = k * (k⁻¹ * x) := by group
    rw [hxk]
    exact Subgroup.mul_mem _ hk (Subgroup.mem_sup_right h2)
  let f' : PQuot p' K →* (↥K ⧸ P) :=
    QuotientGroup.map N P (MonoidHom.id ↥K) (fun x hx => Subgroup.mem_comap.2 (Subgroup.mem_sup_left hx))
  let f : PQuot p K →* (↥K ⧸ P) :=
    QuotientGroup.map M P (MonoidHom.id ↥K) (fun x hx => Subgroup.mem_comap.2 (Subgroup.mem_sup_right hx))
  have hf's : Function.Surjective f' := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective P y
    exact ⟨QuotientGroup.mk' N x, rfl⟩
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective P y
    exact ⟨QuotientGroup.mk' M x, rfl⟩
  have hkerf' : f'.ker ≤ Subgroup.center (PQuot p' K) := by
    intro z hz
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N z
    have hk : k ∈ P := by
      have h1 : (QuotientGroup.mk' P k : ↥K ⧸ P) = 1 := hz
      exact (QuotientGroup.eq_one_iff k).1 h1
    have hmem : (QuotientGroup.mk' N k : PQuot p' K) ∈ P.map (QuotientGroup.mk' N) :=
      Subgroup.mem_map.2 ⟨k, hk, rfl⟩
    exact le_center_of_normal_of_isQuasisimple hQ' (inferInstance : (P.map (QuotientGroup.mk' N)).Normal)
      hPNne hmem
  have hkerf : f.ker ≤ Subgroup.center (PQuot p K) := by
    intro z hz
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective M z
    have hk : k ∈ P := by
      have h1 : (QuotientGroup.mk' P k : ↥K ⧸ P) = 1 := hz
      exact (QuotientGroup.eq_one_iff k).1 h1
    have hmem : (QuotientGroup.mk' M k : PQuot p K) ∈ P.map (QuotientGroup.mk' M) :=
      Subgroup.mem_map.2 ⟨k, hk, rfl⟩
    exact le_center_of_normal_of_isQuasisimple hQ (inferInstance : (P.map (QuotientGroup.mk' M)).Normal)
      hPMne hmem
  obtain ⟨e'⟩ := psimple_equiv_of_central_surj hQ' f' hf's hkerf'
  obtain ⟨e⟩ := psimple_equiv_of_central_surj hQ f hfs hkerf
  exact ⟨e'.trans e.symm⟩

end CFSG.LocalAnalysis.GLTheoremA
