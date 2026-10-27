module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthRigid
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172V2
public import CFSG.LocalAnalysis.GLTheoremA.S12.Compl123
import CFSG.LocalAnalysis.GLTheoremA.ExcClubList

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.StandardType (GGLabelRigidInput)

variable {G : Type} [Group G] [Finite G] {J : Subgroup G} {p : ℕ}

theorem i167COrth_corner (hb : CatDistinct.OrderBridge) (hJt : Type167J p J)
    (h : catalogIs (PSimple p J) (isOmPA 3 (2 ^ 1))) : False := by
  obtain ⟨-, hv⟩ := S172.v2_isOmPA hb (le_refl 1) h
  rcases hJt with ⟨rfl, n, -, hn5, hc⟩ | ⟨rfl, n, -, hn6, hc⟩ | ⟨n, k, -, hn3, hk5, hk, -, hc⟩
  · obtain ⟨-, -, h2⟩ := S172.v2_isLnA hb (le_refl 1) (by simpa using hc : catalogIs _ (isLnA n (2 ^ 1)))
    have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul hn5 (by omega)
    omega
  · obtain ⟨-, h2⟩ := S172.v2_isOmMA hb (le_refl 1) (by simpa using hc : catalogIs _ (isOmMA n (2 ^ 1)))
    have : 6 * 5 ≤ n * (n - 1) := Nat.mul_le_mul hn6 (by omega)
    omega
  · obtain ⟨-, h2⟩ := S172.v2_isOmPA hb hk hc
    rw [hv] at h2
    by_cases hn : n = 3
    · subst hn
      have : k = 1 := by omega
      have := hk5 this
      omega
    · have h4 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      have h5 : 1 * (n * (n - 1)) ≤ k * (n * (n - 1)) := Nat.mul_le_mul hk le_rfl
      omega

variable (hD : COrthLabelDict) (hRig : GGLabelRigidInput) (hJq : CFSG.Open.IsQuasisimple ↥J)
  (hJp : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* PSimple p J)) (hJt : Type167J p J)
include hD hRig hJq hJp hJt

theorem i167COrth_type_no_unitary {m f : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f)
    (h : catalogIs (PSimple p J) (isUnA m (2 ^ f))) : False := by
  obtain ⟨e⟩ := hJp
  have h' := (catalogIs_congr e).2 h
  rcases hJt with ⟨rfl, n, -, hn5, hc⟩ | ⟨rfl, n, -, hn6, hc⟩ | ⟨n, k, -, hn3, hk5, hk, -, hc⟩
  · exact i167COrth_clash_un_lin hD hRig hJq hm hf hn5 h' ((catalogIs_congr e).2 hc)
  · have hc' : catalogIs (↥J ⧸ Subgroup.center ↥J) (isOmMA n (2 ^ 1)) := by
      simpa using (catalogIs_congr e).2 hc
    exact i167COrth_clash_un_minus hD hRig hJq hm hf (by omega) le_rfl h' hc'
  · exact i167COrth_clash_un_plus hD hRig hJq hm hf hn3 hk (fun h3 => by omega) h'
      ((catalogIs_congr e).2 hc)

theorem i167COrth_type_plus (hb : CatDistinct.OrderBridge) {m a : ℕ} (hm : 3 ≤ m) (ha : 1 ≤ a)
    (h : catalogIs (PSimple p J) (isOmPA m (2 ^ a))) :
    ∃ n k : ℕ, Odd n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ catalogIs (PSimple p J) (isOmPA n (2 ^ k)) ∧
      n = m ∧ k = a := by
  by_cases hc3 : m = 3 ∧ a = 1
  · exfalso
    obtain ⟨rfl, rfl⟩ := hc3
    exact i167COrth_corner hb hJt h
  obtain ⟨e⟩ := hJp
  have h' := (catalogIs_congr e).2 h
  rcases hJt with ⟨rfl, n, -, hn5, hc⟩ | ⟨rfl, n, -, hn6, hc⟩ | ⟨n, k, hn, hn3, hk5, hk, hpk, hc⟩
  · exact (i167COrth_clash_lin_plus hD hRig hJq hn5 hm ha (fun h3 => by omega)
      ((catalogIs_congr e).2 hc) h').elim
  · have hc' : catalogIs (↥J ⧸ Subgroup.center ↥J) (isOmMA n (2 ^ 1)) := by
      simpa using (catalogIs_congr e).2 hc
    exact (i167COrth_clash_plus_minus hD hRig hJq hm ha (fun h3 => by omega) (by omega) le_rfl h' hc').elim
  · obtain ⟨hnm, hka⟩ := i167COrth_agree_plus hD hRig hJq hn3 hk (fun h3 => by omega) hm ha
      (fun h3 => by omega) ((catalogIs_congr e).2 hc) h'
    exact ⟨n, k, hn, hk, hpk, hc, hnm, hka⟩

theorem i167COrth_type_minus {m a : ℕ} (hm : 4 ≤ m) (ha : 1 ≤ a)
    (h : catalogIs (PSimple p J) (isOmMA m (2 ^ a))) :
    p = 3 ∧ ∃ n : ℕ, Even n ∧ catalogIs (PSimple 3 J) (isOmMA n 2) ∧ n = m ∧ a = 1 := by
  obtain ⟨e⟩ := hJp
  have h' := (catalogIs_congr e).2 h
  rcases hJt with ⟨rfl, n, -, hn5, hc⟩ | ⟨rfl, n, hn, hn6, hc⟩ | ⟨n, k, -, hn3, hk5, hk, -, hc⟩
  · exact (i167COrth_clash_lin_minus hD hRig hJq hn5 hm ha ((catalogIs_congr e).2 hc) h').elim
  · have hc' : catalogIs (↥J ⧸ Subgroup.center ↥J) (isOmMA n (2 ^ 1)) := by
      simpa using (catalogIs_congr e).2 hc
    obtain ⟨hnm, hka⟩ := i167COrth_agree_minus hD hRig hJq (by omega) le_rfl hm ha hc' h'
    exact ⟨rfl, n, hn, hc, hnm, hka.symm⟩
  · exact (i167COrth_clash_plus_minus hD hRig hJq hn3 hk (fun h3 => by omega) hm ha
      ((catalogIs_congr e).2 hc) h').elim

end CFSG.LocalAnalysis.GLTheoremA.I167

end
