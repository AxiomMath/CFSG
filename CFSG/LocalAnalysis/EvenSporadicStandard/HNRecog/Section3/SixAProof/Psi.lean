module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.ModelTheta

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z x : G}

structure SixAIso (a x : G) where
  e : ↥(Gxy a (x * (a * x) ^ 3)) ≃* Sym 7
  map_b : ∀ hb : (a * x) ^ 3 ∈ Gxy a (x * (a * x) ^ 3), e ⟨(a * x) ^ 3, hb⟩ = sixASigma

theorem sixA_exists_iso (h : IsF5Type a z) (hx : x ∈ orb6A a a) (hS : S7Facts a z) :
    Nonempty (SixAIso a x) := by
  have hy := sixA_y_mem_orb3A h hx
  obtain ⟨φ⟩ := hS.shape _ hy
  have hb := sixA_b_mem_Gxy_y h hx
  have hct : (φ ⟨(a * x) ^ 3, hb⟩).cycleType = {2} :=
    (hS.cycleType _ hy φ ⟨(a * x) ^ 3, hb⟩).1 (sixA_b_mem_orb2A h hx)
  have hconj : IsConj (φ ⟨(a * x) ^ 3, hb⟩) sixASigma := by
    rw [Equiv.Perm.isConj_iff_cycleType_eq, hct, sixA_cycleType_sigma]
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  refine ⟨⟨φ.trans (MulAut.conj c), fun hb' => ?_⟩⟩
  simpa [MulEquiv.trans_apply, MulAut.conj_apply] using hc

open Classical in
@[expose] noncomputable def SixAIso.f (ψ : SixAIso a x) (g : G) : Sym 7 :=
  if hg : g ∈ Gxy a (x * (a * x) ^ 3) then ψ.e ⟨g, hg⟩ else 1

theorem SixAIso.f_apply (ψ : SixAIso a x) {g : G} (hg : g ∈ Gxy a (x * (a * x) ^ 3)) :
    ψ.f g = ψ.e ⟨g, hg⟩ := by
  unfold SixAIso.f
  exact dif_pos hg

theorem SixAIso.f_mul (ψ : SixAIso a x) {g g' : G} (hg : g ∈ Gxy a (x * (a * x) ^ 3))
    (hg' : g' ∈ Gxy a (x * (a * x) ^ 3)) : ψ.f (g * g') = ψ.f g * ψ.f g' := by
  rw [ψ.f_apply (mul_mem hg hg'), ψ.f_apply hg, ψ.f_apply hg']
  exact map_mul ψ.e ⟨g, hg⟩ ⟨g', hg'⟩

theorem SixAIso.f_one (ψ : SixAIso a x) : ψ.f 1 = 1 := by
  rw [ψ.f_apply (one_mem _)]
  exact map_one ψ.e

theorem SixAIso.f_inj (ψ : SixAIso a x) {g g' : G} (hg : g ∈ Gxy a (x * (a * x) ^ 3))
    (hg' : g' ∈ Gxy a (x * (a * x) ^ 3)) : ψ.f g = ψ.f g' ↔ g = g' := by
  rw [ψ.f_apply hg, ψ.f_apply hg']
  constructor
  · intro hh
    exact congrArg Subtype.val (ψ.e.injective hh)
  · rintro rfl
    rfl

theorem SixAIso.f_inv (ψ : SixAIso a x) {g : G} (hg : g ∈ Gxy a (x * (a * x) ^ 3)) :
    ψ.f g⁻¹ = (ψ.f g)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← ψ.f_mul (inv_mem hg) hg, inv_mul_cancel, ψ.f_one]

theorem SixAIso.f_conj (ψ : SixAIso a x) {k c : G} (hk : k ∈ Gxy a (x * (a * x) ^ 3))
    (hc : c ∈ Gxy a (x * (a * x) ^ 3)) :
    ψ.f (k * c * k⁻¹) = ψ.f k * ψ.f c * (ψ.f k)⁻¹ := by
  rw [ψ.f_mul (mul_mem hk hc) (inv_mem hk), ψ.f_mul hk hc, ψ.f_inv hk]

theorem SixAIso.f_b (ψ : SixAIso a x) (h : IsF5Type a z) (hx : x ∈ orb6A a a) :
    ψ.f ((a * x) ^ 3) = sixASigma := by
  rw [ψ.f_apply (sixA_b_mem_Gxy_y h hx)]
  exact ψ.map_b _

theorem SixAIso.f_mul_b (ψ : SixAIso a x) (h : IsF5Type a z) (hx : x ∈ orb6A a a) {g : G}
    (hg : g ∈ Gxy a (x * (a * x) ^ 3)) : ψ.f ((a * x) ^ 3 * g) = sixASigma * ψ.f g := by
  rw [ψ.f_mul (sixA_b_mem_Gxy_y h hx) hg, ψ.f_b h hx]

theorem SixAIso.f_mem_cent (ψ : SixAIso a x) (h : IsF5Type a z) (hx : x ∈ orb6A a a) {g : G}
    (hg : g ∈ Gxy a x) : ψ.f g ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7)) := by
  have hgy : g ∈ Gxy a (x * (a * x) ^ 3) := sixA_Gxy_le a x hg
  have hby := sixA_b_mem_Gxy_y h hx
  have hc : g * (a * x) ^ 3 = (a * x) ^ 3 * g := sixA_comm_b_of_mem hg
  rw [Subgroup.mem_centralizer_singleton_iff, ← ψ.f_b h hx, ← ψ.f_mul hgy hby,
    ← ψ.f_mul hby hgy, hc]

theorem SixAIso.mem_of_f_mem_cent (ψ : SixAIso a x) (h : IsF5Type a z) (hx : x ∈ orb6A a a)
    {g : G} (hg : g ∈ Gxy a (x * (a * x) ^ 3))
    (hs : ψ.f g ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7))) : g ∈ Gxy a x := by
  have hby := sixA_b_mem_Gxy_y h hx
  rw [Subgroup.mem_centralizer_singleton_iff, ← ψ.f_b h hx, ← ψ.f_mul hg hby,
    ← ψ.f_mul hby hg] at hs
  have hc : g * (a * x) ^ 3 = (a * x) ^ 3 * g :=
    (ψ.f_inj (mul_mem hg hby) (mul_mem hby hg)).1 hs
  exact (sixA_mem_Gxy_iff h hx).2 ⟨hg, hc⟩

theorem SixAIso.exists_of_mem_cent (ψ : SixAIso a x) (h : IsF5Type a z) (hx : x ∈ orb6A a a)
    {s : Sym 7} (hs : s ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7))) :
    ∃ g ∈ Gxy a x, ψ.f g = s := by
  have hgy : ((ψ.e.symm s : ↥(Gxy a (x * (a * x) ^ 3))) : G) ∈ Gxy a (x * (a * x) ^ 3) :=
    (ψ.e.symm s).2
  have hfg : ψ.f (ψ.e.symm s : G) = s := by
    rw [ψ.f_apply hgy]
    simp
  exact ⟨_, ψ.mem_of_f_mem_cent h hx hgy (by rw [hfg]; exact hs), hfg⟩

theorem SixAIso.f_sq_of_orderOf (ψ : SixAIso a x) {t : G} (ht : t ∈ Gxy a (x * (a * x) ^ 3))
    (ht2 : orderOf t = 2) : ψ.f t ^ 2 = 1 ∧ ψ.f t ≠ 1 := by
  have h1 : t * t = 1 := by rw [← pow_two]; rw [← ht2]; exact pow_orderOf_eq_one t
  have hne : t ≠ 1 := by
    intro h1'
    rw [h1', orderOf_one] at ht2
    omega
  refine ⟨?_, ?_⟩
  · rw [pow_two, ← ψ.f_mul ht ht, h1, ψ.f_one]
  · intro hf
    exact hne ((ψ.f_inj ht (one_mem _)).1 (hf.trans ψ.f_one.symm))

theorem SixAIso.f_ne_sigma (ψ : SixAIso a x) (h : IsF5Type a z) (hx : x ∈ orb6A a a) {t : G}
    (ht : t ∈ Gxy a (x * (a * x) ^ 3)) (htb : t ≠ (a * x) ^ 3) : ψ.f t ≠ sixASigma := by
  intro hf
  exact htb ((ψ.f_inj ht (sixA_b_mem_Gxy_y h hx)).1 (hf.trans (ψ.f_b h hx).symm))

theorem SixAIso.exists_invol (ψ : SixAIso a x) (h : IsF5Type a z) (hx : x ∈ orb6A a a)
    {s : Sym 7} (hs : s ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7))) (hs2 : s ^ 2 = 1)
    (hs1 : s ≠ 1) (hsσ : s ≠ sixASigma) :
    ∃ t ∈ Gxy a x, orderOf t = 2 ∧ t ≠ (a * x) ^ 3 ∧ ψ.f t = s := by
  obtain ⟨g, hg, hfg⟩ := ψ.exists_of_mem_cent h hx hs
  have hgy : g ∈ Gxy a (x * (a * x) ^ 3) := sixA_Gxy_le a x hg
  have hg2 : g ^ 2 = 1 := by
    rw [pow_two]
    refine (ψ.f_inj (mul_mem hgy hgy) (one_mem _)).1 ?_
    rw [ψ.f_mul hgy hgy, hfg, ← pow_two, hs2, ψ.f_one]
  have hg1 : g ≠ 1 := by
    intro h1
    apply hs1
    rw [← hfg, h1, ψ.f_one]
  refine ⟨g, hg, orderOf_eq_prime hg2 hg1, ?_, hfg⟩
  intro hgb
  apply hsσ
  rw [← hfg, hgb, ψ.f_b h hx]

end CFSG.EvenSporadicStandard.HNRecog.Section3
