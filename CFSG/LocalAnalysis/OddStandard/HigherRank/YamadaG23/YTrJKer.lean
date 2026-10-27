module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YJ
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTransport

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mem_zL_iff {x : G} : x ∈ zL L ↔ x ∈ L ∧ x ∈ centralizer (L : Set G) := by
  rw [zL, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← hyx]
    exact ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun z hz =>
      by simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hy (⟨z, hz⟩ : ↥L))⟩
  · rintro ⟨hxL, hxC⟩
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by simpa using Subgroup.mem_centralizer_iff.mp hxC (g : G) g.2)

theorem zL_le : zL L ≤ L := Subgroup.map_subtype_le (center ↥L)

theorem actsAs_one_iff_mem_zL [Group.IsPerfect ↥L] {x : G} (hx : x ∈ L) :
    ActsAs L x (1 : MulAut (L ⧸ center L)) ↔ x ∈ zL L := by
  rw [actsAs_one_iff L]
  exact ⟨fun h => (mem_zL_iff (L := L)).mpr ⟨hx, h⟩, fun h => ((mem_zL_iff (L := L)).mp h).2⟩

theorem jSub_zL [Group.IsPerfect ↥L] : jSub L (zL L) = ⊥ := by
  apply le_antisymm
  · rw [← jSub_centralizer L]
    exact jSub_mono L fun x hx => ((mem_zL_iff (L := L)).mp hx).2
  · exact bot_le

theorem jSub_bot : jSub L (⊥ : Subgroup G) = ⊥ := by
  apply le_antisymm
  · intro α hα
    obtain ⟨g, hg, hag⟩ := (mem_jSub L).mp hα
    rw [Subgroup.mem_bot] at hg
    rw [hg] at hag
    rw [Subgroup.mem_bot]
    exact actsAs_unique L hag (actsAs_one L)
  · exact bot_le

theorem jSub_sup {V W : Subgroup G} (hV : V ≤ normalizer (L : Set G))
    (hW : W ≤ normalizer (L : Set G)) : jSub L (V ⊔ W) = jSub L V ⊔ jSub L W := by
  simp only [jSub, Subgroup.subgroupOf_sup hV hW, Subgroup.map_sup]

theorem jSub_sup_zL [Group.IsPerfect ↥L] {V : Subgroup G} (hV : V ≤ L) :
    jSub L (zL L ⊔ V) = jSub L V := by
  rw [jSub_sup (V := zL L) (W := V) ((zL_le (L := L)).trans L.le_normalizer)
    (hV.trans L.le_normalizer), jSub_zL (L := L), bot_sup_eq]

theorem mem_zL_sup_of_actsAs [Group.IsPerfect ↥L] {V : Subgroup G} (hV : V ≤ L) {x : G}
    (hx : x ∈ L) {α : MulAut (L ⧸ center L)} (hxα : ActsAs L x α) (hα : α ∈ jSub L V) :
    x ∈ zL L ⊔ V := by
  obtain ⟨v, hv, hvα⟩ := (mem_jSub L).mp hα
  have hvL : v ∈ L := hV hv
  have hxvL : x * v⁻¹ ∈ L := L.mul_mem hx (L.inv_mem hvL)
  have hact : ActsAs L (x * v⁻¹) (1 : MulAut (L ⧸ center L)) := by
    have h := actsAs_mul L hxα (actsAs_inv L hvα)
    simpa using h
  have hz : x * v⁻¹ ∈ zL L := (actsAs_one_iff_mem_zL hxvL).mp hact
  have : x = (x * v⁻¹) * v := by group
  rw [this]
  exact Subgroup.mul_mem_sup hz hv

private lemma exists_mul_of_mem_zL_sup {V : Subgroup G} (hVL : V ≤ L) {x : G}
    (hx : x ∈ zL L ⊔ V) : ∃ c ∈ zL L, ∃ v ∈ V, c * v = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun y _ => ∃ c ∈ zL L, ∃ v ∈ V, c * v = y)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, V.one_mem, by simp⟩
    · exact ⟨1, (zL L).one_mem, y, hy, by simp⟩
  · exact ⟨1, (zL L).one_mem, 1, V.one_mem, by simp⟩
  · intro a b _ _ ⟨c₁, hc₁, v₁, hv₁, hcv₁⟩ ⟨c₂, hc₂, v₂, hv₂, hcv₂⟩
    have hcomm : c₂ * v₁ = v₁ * c₂ := by
      have hcC : c₂ ∈ centralizer (L : Set G) := ((mem_zL_iff (L := L)).mp hc₂).2
      exact (Subgroup.mem_centralizer_iff.mp hcC v₁ (hVL hv₁)).symm
    refine ⟨c₁ * c₂, mul_mem hc₁ hc₂, v₁ * v₂, mul_mem hv₁ hv₂, ?_⟩
    rw [← hcv₁, ← hcv₂]
    calc c₁ * c₂ * (v₁ * v₂) = c₁ * (c₂ * v₁) * v₂ := by group
      _ = c₁ * (v₁ * c₂) * v₂ := by rw [hcomm]
      _ = c₁ * v₁ * (c₂ * v₂) := by group
  · intro a _ ⟨c, hc, v, hv, hcv⟩
    refine ⟨c⁻¹, inv_mem hc, v⁻¹, inv_mem hv, ?_⟩
    have hcomm : v * c = c * v := by
      have hcC : c ∈ centralizer (L : Set G) := ((mem_zL_iff (L := L)).mp hc).2
      exact Subgroup.mem_centralizer_iff.mp hcC v (hVL hv)
    rw [← hcv]
    calc c⁻¹ * v⁻¹ = (v * c)⁻¹ := (mul_inv_rev v c).symm
      _ = (c * v)⁻¹ := by rw [hcomm]

theorem mem_of_mem_zL_sup (hZ : Odd (Nat.card ↥(center ↥L))) {V : Subgroup G} (hVL : V ≤ L)
    (hV : IsPGroup 2 ↥V) {x : G} (hx : x ∈ zL L ⊔ V) (h2 : IsPGroup 2 ↥(zpowers x)) :
    x ∈ V := by
  obtain ⟨c, hc, v, hv, hcv⟩ := exists_mul_of_mem_zL_sup (L := L) hVL hx
  have hcC : c ∈ centralizer (L : Set G) := ((mem_zL_iff (L := L)).mp hc).2
  have hcL : c ∈ L := ((mem_zL_iff (L := L)).mp hc).1
  have hvL : v ∈ L := hVL hv
  have hcomm_cv : v * c = c * v := Subgroup.mem_centralizer_iff.mp hcC v hvL
  have hxveq : x * v = v * x := by
    rw [← hcv]
    calc c * v * v = c * (v * v) := by group
      _ = v * c * v := by rw [hcomm_cv]; group
      _ = v * (c * v) := by group
  have hxv : Commute x v := (commute_iff_eq x v).mpr hxveq
  obtain ⟨m1, hm1⟩ := isPGroup_iff_exists_pow_pow_eq_one.mp hV
  obtain ⟨m2, hm2⟩ := isPGroup_iff_exists_pow_pow_eq_one.mp h2
  have hvpow : v ^ 2 ^ m1 = 1 := by simpa using hm1 ⟨v, hv⟩
  have hxpow : x ^ 2 ^ m2 = 1 := by simpa using hm2 ⟨x, Subgroup.mem_zpowers x⟩
  set M := m1 + m2 with hM
  have hxM : x ^ 2 ^ M = 1 := by
    rw [hM, pow_add, mul_comm, pow_mul, hxpow, one_pow]
  have hvM : v ^ 2 ^ M = 1 := by
    rw [hM, pow_add, pow_mul, hvpow, one_pow]
  have hcM : c ^ 2 ^ M = 1 := by
    have hc_eq : c = x * v⁻¹ := by rw [← hcv]; group
    rw [hc_eq, hxv.inv_right.mul_pow (2 ^ M), inv_pow, hvM, inv_one, hxM, mul_one]
  have hcdiv : orderOf c ∣ 2 ^ M := orderOf_dvd_of_pow_eq_one hcM
  have hcenter : (⟨c, hcL⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by simpa using Subgroup.mem_centralizer_iff.mp hcC (g : G) g.2)
  have hdvd : orderOf (⟨c, hcL⟩ : ↥L) ∣ Nat.card ↥(center ↥L) :=
    (center ↥L).orderOf_dvd_natCard hcenter
  have hdvd' : orderOf c ∣ Nat.card ↥(center ↥L) := by
    rw [Subgroup.orderOf_mk c hcL] at hdvd
    exact hdvd
  have hodd : Odd (orderOf c) := Odd.of_dvd_nat hZ hdvd'
  have hc_one : c = 1 := by
    rw [← orderOf_eq_one_iff]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hcdiv
    cases j with
    | zero => simpa using hj
    | succ j =>
        exfalso
        exact (Nat.not_even_iff_odd.mpr hodd)
          (by rw [hj]; exact Even.pow_of_ne_zero even_two (Nat.succ_ne_zero j))
  rw [← hcv, hc_one, one_mul]
  exact hv

theorem mem_jSub_iff_mem [Group.IsPerfect ↥L] (hZ : Odd (Nat.card ↥(center ↥L))) {W : Subgroup G}
    (hWL : W ≤ L) (hW : IsPGroup 2 ↥W) {x : G} (hx : x ∈ L) (hx2 : IsPGroup 2 ↥(zpowers x))
    {α : MulAut (L ⧸ center L)} (hxα : ActsAs L x α) : α ∈ jSub L W ↔ x ∈ W := by
  constructor
  · intro hα
    exact mem_of_mem_zL_sup (L := L) hZ hWL hW
      (mem_zL_sup_of_actsAs (L := L) hWL hx hxα hα) hx2
  · intro hxW
    exact (mem_jSub L).mpr ⟨x, hxW, hxα⟩

theorem le_of_jSub_le [Group.IsPerfect ↥L] (hZ : Odd (Nat.card ↥(center ↥L))) {V W : Subgroup G}
    (hVL : V ≤ L) (hV : IsPGroup 2 ↥V) (hWL : W ≤ L) (hW : IsPGroup 2 ↥W)
    (h : jSub L V ≤ jSub L W) : V ≤ W := by
  intro x hxV
  have hxL : x ∈ L := hVL hxV
  have hxα : ActsAs L x (jHom L ⟨x, Subgroup.le_normalizer hxL⟩) :=
    jHom_actsAs L ⟨x, Subgroup.le_normalizer hxL⟩
  have hmem : jHom L ⟨x, Subgroup.le_normalizer hxL⟩ ∈ jSub L W :=
    h ((mem_jSub L).mpr ⟨x, hxV, hxα⟩)
  refine (mem_jSub_iff_mem (L := L) hZ hWL hW hxL ?_ hxα).mp hmem
  exact hV.of_injective (Subgroup.inclusion (Subgroup.zpowers_le.mpr hxV))
    (Subgroup.inclusion_injective _)

theorem jSub_le_iff [Group.IsPerfect ↥L] {V W : Subgroup G} (hV : V ≤ L) (hW : W ≤ L)
    (hzW : zL L ≤ W) : jSub L V ≤ jSub L W ↔ V ≤ W := by
  constructor
  · intro h x hxV
    have hxL : x ∈ L := hV hxV
    have hxα : ActsAs L x (jHom L ⟨x, Subgroup.le_normalizer hxL⟩) :=
      jHom_actsAs L ⟨x, Subgroup.le_normalizer hxL⟩
    have hmem : jHom L ⟨x, Subgroup.le_normalizer hxL⟩ ∈ jSub L W :=
      h ((mem_jSub L).mpr ⟨x, hxV, hxα⟩)
    have hxsup : x ∈ zL L ⊔ W := mem_zL_sup_of_actsAs (L := L) hW hxL hxα hmem
    rw [sup_eq_right.mpr hzW] at hxsup
    exact hxsup
  · intro h
    exact jSub_mono L h

theorem jSub_inj [Group.IsPerfect ↥L] {V W : Subgroup G} (hV : V ≤ L) (hW : W ≤ L)
    (hzV : zL L ≤ V) (hzW : zL L ≤ W) (h : jSub L V = jSub L W) : V = W :=
  le_antisymm ((jSub_le_iff (L := L) hV hW hzW).mp h.le)
    ((jSub_le_iff (L := L) hW hV hzV).mp h.ge)

theorem jSub_inf [Group.IsPerfect ↥L] {V W : Subgroup G} (hV : V ≤ L) (hW : W ≤ L)
    (hzV : zL L ≤ V) : jSub L (V ⊓ W) = jSub L V ⊓ jSub L W := by
  refine le_antisymm ?_ ?_
  · exact le_inf (jSub_mono L inf_le_left) (jSub_mono L inf_le_right)
  · intro α hα
    obtain ⟨hv, hw⟩ := Subgroup.mem_inf.mp hα
    obtain ⟨v, hvV, hvα⟩ := (mem_jSub L).mp hv
    obtain ⟨w, hwW, hwα⟩ := (mem_jSub L).mp hw
    have htriv : ActsAs L (v * w⁻¹) (1 : MulAut (L ⧸ center L)) := by
      have h := actsAs_mul L hvα (actsAs_inv L hwα)
      simpa using h
    have hdL : v * w⁻¹ ∈ L := L.mul_mem (hV hvV) (L.inv_mem (hW hwW))
    have hdzL : v * w⁻¹ ∈ zL L := (actsAs_one_iff_mem_zL hdL).mp htriv
    have hwV : w ∈ V := by
      have hmem : (v * w⁻¹)⁻¹ * v ∈ V := V.mul_mem (V.inv_mem (hzV hdzL)) hvV
      have heq : (v * w⁻¹)⁻¹ * v = w := by group
      rw [heq] at hmem
      exact hmem
    exact (mem_jSub L).mpr ⟨w, ⟨hwV, hwW⟩, hwα⟩

theorem jSub_closure_of_actsAs (S : Set G) (hS : ∀ x ∈ S, x ∈ normalizer (L : Set G))
    (f : G → MulAut (L ⧸ center L)) (hf : ∀ x ∈ S, ActsAs L x (f x)) :
    jSub L (closure S) = closure (f '' S) := by
  apply le_antisymm
  · intro α hα
    obtain ⟨g, hg, hag⟩ := (mem_jSub L).mp hα
    have key : ∀ g ∈ closure S, ∃ β ∈ closure (f '' S), ActsAs L g β := by
      intro g hg
      refine Subgroup.closure_induction
        (p := fun g _ => ∃ β ∈ closure (f '' S), ActsAs L g β) ?_ ?_ ?_ ?_ hg
      · intro x hx
        exact ⟨f x, Subgroup.subset_closure ⟨x, hx, rfl⟩, hf x hx⟩
      · exact ⟨1, one_mem _, actsAs_one L⟩
      · intro a b _ _ ⟨β, hβ, haβ⟩ ⟨γ, hγ, haγ⟩
        exact ⟨β * γ, mul_mem hβ hγ, actsAs_mul L haβ haγ⟩
      · intro a _ ⟨β, hβ, haβ⟩
        exact ⟨β⁻¹, inv_mem hβ, actsAs_inv L haβ⟩
    obtain ⟨β, hβ, haβ⟩ := key g hg
    rwa [actsAs_unique L hag haβ]
  · rw [Subgroup.closure_le]
    rintro y ⟨x, hxS, rfl⟩
    exact (mem_jSub L).mpr ⟨x, Subgroup.subset_closure hxS, hf x hxS⟩

end CFSG.OddStandard.HigherRank.YamadaG23
