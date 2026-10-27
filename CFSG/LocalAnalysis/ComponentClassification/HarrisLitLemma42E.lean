module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma42
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

theorem isSylowOf_of_card_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup p P)
    (h : ∀ Q : Subgroup G, Q ≤ K → IsPGroup p Q → P ≤ Q → Nat.card Q ≤ Nat.card P) :
    IsSylowOf p P K := by
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype : IsPGroup p (P.subgroupOf K)).exists_le_sylow
  have hPQ : P ≤ (Q : Subgroup K).map K.subtype := fun x hx => ⟨⟨x, hPK hx⟩, hQ hx, rfl⟩
  have hle := h _ (map_subtype_le _) (Q.isPGroup'.map K.subtype) hPQ
  exact ⟨Q, (Subgroup.eq_of_le_of_card_ge hPQ hle).symm⟩

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

theorem card_le_of_field [Finite X] (hKC : AutPSL2CentralizerInput) (h : Standing t L p f)
    {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))} {w : X} (hL : Lift h hS w)
    {τ : X} (hτ : τ ∈ centralizer ({t} : Set X)) (hτf : IsFieldAutPSL2 (h.rho ⟨τ, hτ⟩))
    {Q : Subgroup X} (hQH : Q ≤ centralizer ({t} : Set X)) (hQτ : Q ≤ centralizer {τ})
    (hQ : IsPGroup 2 Q) :
    Nat.card Q ≤ 2 * Nat.card (((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
      innAut (Bar L)) ⊔ zpowers (h.rho ⟨w, hS.le hL.mem⟩) : Subgroup (MulAut (Bar L))) := by
  have htH : t ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  have ht2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.config.orderOf_eq, pow_one])
  have hQn : Q ≤ normalizer (zpowers t : Set X) := fun x hx => by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    have hc : Commute x t := mem_centralizer_singleton_iff.mp (hQH hx)
    exact (hc.zpow_right j).eq.symm
  have hQ' : IsPGroup 2 (Q ⊔ zpowers t : Subgroup X) := hQ.to_sup_of_normal_right' ht2 hQn
  have hQ'H : Q ⊔ zpowers t ≤ centralizer ({t} : Set X) := sup_le hQH (zpowers_le.mpr htH)
  have hQ'τ : Q ⊔ zpowers t ≤ centralizer ({τ} : Set X) := by
    refine sup_le hQτ (zpowers_le.mpr ?_)
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.mp hτ).symm
  obtain ⟨S'₀, hS'₀⟩ := (hQ'.comap_subtype : IsPGroup 2 ((Q ⊔ zpowers t).subgroupOf
    (centralizer ({t} : Set X)))).exists_le_sylow
  have hS' : IsSylowOf 2 ((S'₀ : Subgroup ↥(centralizer ({t} : Set X))).map
      (centralizer ({t} : Set X)).subtype) (centralizer ({t} : Set X)) := ⟨S'₀, rfl⟩
  have hQ'S' : Q ⊔ zpowers t ≤ (S'₀ : Subgroup ↥(centralizer ({t} : Set X))).map
      (centralizer ({t} : Set X)).subtype := fun x hx => ⟨⟨x, hQ'H hx⟩, hS'₀ hx, rfl⟩
  have hcard := h.card_eq_two_mul hS' hQ'S' (mem_sup_right (mem_zpowers t))
  obtain ⟨-, hcent⟩ := hKC (Bar L) p f h.config.prime h.config.ne_two
    (h.dihedral.even p f h.config.prime h.config.ne_two h.config.lieModel) h.sixteen
    h.config.lieModel
  have hSyl := h.isSylowOf_rho hS
  have hle := hcent h.rho.range h.innAut_le_range _ hSyl.le hSyl.exists_sylow_eq_subgroupOf
    _ hL.data (h.rho ⟨τ, hτ⟩) ⟨_, rfl⟩ hτf (((Q ⊔ zpowers t).subgroupOf _).map h.rho)
    (map_le_range _ _) (hQ'.comap_subtype.map _) (by
      rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hQ'τ hy)))
  calc Nat.card Q ≤ Nat.card (Q ⊔ zpowers t : Subgroup X) :=
        Subgroup.card_le_of_le le_sup_left
    _ = _ := hcard
    _ ≤ _ := Nat.mul_le_mul_left 2 hle

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem map_rho_T [Finite X] (hσ : Setup42 h hS w z) :
    ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).subgroupOf (centralizer ({t} : Set X))).map h.rho =
      ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) ⊔
        zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩) := by
  have hR := h.map_rho_inf_innAut hS
  apply le_antisymm
  · rw [← hσ.lift.data.centralizer_v₀]
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨⟨x, hσ.T_le hx, rfl⟩, ?_⟩
    have hxu : (x : X) ∈ S ⊓ centralizer {w ^ (orderOf w / 2)} := by
      rw [hσ.centralizer_u]
      exact hx
    rw [mem_centralizer_singleton_iff, ← hσ.rho_u, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hxu.2)
  · refine sup_le ?_ ?_
    · rw [hR]
      exact map_mono fun x hx => mem_sup_left (mem_sup_right hx)
    · rw [zpowers_le]
      exact ⟨⟨w, hS.le hσ.lift.mem⟩, mem_sup_right (mem_zpowers w), rfl⟩

theorem card_T [Finite X] (hσ : Setup42 h hS w z) :
    Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) =
      2 * Nat.card (((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L)) ⊔
        zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩) : Subgroup (MulAut (Bar L))) := by
  rw [h.card_eq_two_mul hS hσ.T_le (mem_sup_left (mem_sup_left (mem_zpowers t))), hσ.map_rho_T]

theorem isFieldAut_rho [Finite X] (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z)
    (i j : ℕ) (hτ : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ centralizer ({t} : Set X)) :
    IsFieldAutPSL2 (h.rho ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hτ⟩) := by
  have hdata := hσ.lift.data
  set v := h.rho ⟨w, hS.le hσ.lift.mem⟩ with hv
  have hzH : z ∈ centralizer ({t} : Set X) := hS.le hσ.z_mem.1
  have htH : t ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  have hzInn : h.rho ⟨z, hzH⟩ ∈ innAut (Bar L) :=
    ⟨QuotientGroup.mk ⟨z, hσ.z_mem.2⟩, (h.rho_of_mem ⟨z, hσ.z_mem.2⟩).symm⟩
  have hzS : h.rho ⟨z, hzH⟩ ∈ (S.subgroupOf (centralizer ({t} : Set X))).map h.rho :=
    ⟨⟨z, hzH⟩, hσ.z_mem.1, rfl⟩
  have hzj : h.rho ⟨z, hzH⟩ ^ j ∈
      (S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓ innAut (Bar L) :=
    Subgroup.mem_inf.mpr ⟨pow_mem hzS j, pow_mem hzInn j⟩
  have hc : Commute (h.rho ⟨z, hzH⟩ ^ j) (v ^ (orderOf v / 2)) := hdata.comm_v₀ _ hzj
  have hsplit : (⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hτ⟩ : ↥(centralizer ({t} : Set X))) =
      ⟨w ^ (orderOf w / 2), hS.le hσ.u_mem⟩ * ⟨t, htH⟩ ^ i * ⟨z, hzH⟩ ^ j := rfl
  have hρ : h.rho ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hτ⟩ =
      h.rho ⟨z, hzH⟩ ^ j * v ^ (orderOf v / 2) := by
    rw [hsplit, map_mul, map_mul, map_pow, map_pow, h.rho_t, one_pow, mul_one, hσ.rho_u]
    exact hc.eq.symm
  have hv02 : (v ^ (orderOf v / 2)) ^ 2 = 1 := by
    rw [← hσ.rho_u, ← map_pow]
    have : (⟨w ^ (orderOf w / 2), hS.le hσ.u_mem⟩ : ↥(centralizer ({t} : Set X))) ^ 2 = 1 :=
      Subtype.ext hσ.lift.sq_u
    rw [this, map_one]
  have hz2 : h.rho ⟨z, hzH⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨z, hzH⟩ : ↥(centralizer ({t} : Set X))) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← hσ.z_order, pow_orderOf_eq_one, Subgroup.coe_one])
    rw [this, map_one]
  have hsq : (h.rho ⟨z, hzH⟩ ^ j * v ^ (orderOf v / 2)) ^ 2 = 1 := by
    rw [hc.mul_pow, ← pow_mul, mul_comm j, pow_mul, hz2, one_pow, one_mul, hv02]
  obtain ⟨hfield, -⟩ := hKC (Bar L) p f h.config.prime h.config.ne_two
    (h.dihedral.even p f h.config.prime h.config.ne_two h.config.lieModel) h.sixteen
    h.config.lieModel
  rw [hρ]
  exact hfield _ hdata.field₀ _ (pow_mem hzInn j) hsq

theorem isSylowOf_centralizer [Finite X] (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    IsSylowOf 2 (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w)
      (centralizer ({t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) := by
  have hτS : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ S :=
    S.mul_mem (S.mul_mem hσ.u_mem (S.pow_mem (h.t_mem hS) i)) (S.pow_mem hσ.z_mem.1 j)
  have hτX : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ closure {t, w ^ (orderOf w / 2), z} :=
    mul_mem (mul_mem (subset_closure (by simp)) (pow_mem (subset_closure (by simp)) i))
      (pow_mem (subset_closure (by simp)) j)
  refine isSylowOf_of_card_le (le_inf (hσ.T_le.trans hS.le) fun g hg =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hσ.X_le_center_T hτX).2 g hg))
    (hS.isPGroup.to_le hσ.T_le) fun Q hQ hQ2 _ => ?_
  rw [hσ.card_T]
  exact h.card_le_of_field hKC hσ.lift (hS.le hτS) (hσ.isFieldAut_rho hKC i j _)
    (hQ.trans inf_le_left) (hQ.trans inf_le_right) hQ2

theorem isSylowOf_centralizer_X [Finite X] (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) :
    IsSylowOf 2 (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w)
      (centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X)) := by
  have h0 := hσ.isSylowOf_centralizer hKC 0 0
  simp only [pow_zero, mul_one] at h0
  refine h0.of_le (fun g hg => mem_centralizer_iff.mpr fun x hx =>
    (mem_centralizer_iff.mp (hσ.X_le_center_T hx).2 g hg).symm) fun g hg => ⟨?_, ?_⟩
  · exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hg t (subset_closure (by simp))).symm
  · exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hg _ (subset_closure (by simp))).symm

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
