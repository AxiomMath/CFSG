module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YHyp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YJS
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAFacts
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem b₁_mem_A (s : Setting3 G L) : s.fr.b₁ ∈ s.fr.A :=
  Subgroup.subset_closure (by simp)

private theorem z_mem_A (s : Setting3 G L) : s.fr.z ∈ s.fr.A := by
  rw [SFrame.z]
  exact Subgroup.pow_mem s.fr.A (b₁_mem_A s) 2

private theorem A_le_S (s : Setting3 G L) : s.fr.A ≤ s.fr.S :=
  Subgroup.closure_mono (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto)

private theorem z_mem_S (s : Setting3 G L) : s.fr.z ∈ s.fr.S := A_le_S s (z_mem_A s)

private theorem Z_le_S (s : Setting3 G L) : s.fr.Z ≤ s.fr.S := by
  rw [SFrame.Z]
  exact Subgroup.zpowers_le.mpr (z_mem_S s)

private theorem commutator_mem_A (s : Setting3 G L) {a b : G} (ha : a ∈ s.fr.A)
    (hb : b ∈ s.fr.A) : ⁅a, b⁆ ∈ s.fr.A := by
  rw [commutatorElement_def]
  exact s.fr.A.mul_mem (s.fr.A.mul_mem (s.fr.A.mul_mem ha hb) (s.fr.A.inv_mem ha))
    (s.fr.A.inv_mem hb)

private theorem actsAs_pow {g : G} {α : MulAut (L ⧸ center L)} (h : ActsAs L g α) (n : ℕ) :
    ActsAs L (g ^ n) (α ^ n) := by
  induction n with
  | zero => simpa using actsAs_one L
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact actsAs_mul L ih h

private theorem actsAs_comm {a b : G} {α β : MulAut (L ⧸ center L)}
    (ha : ActsAs L a α) (hb : ActsAs L b β) : ActsAs L ⁅a, b⁆ ⁅α, β⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have h1 : ActsAs L (a * b) (α * β) := actsAs_mul L ha hb
  have h2 : ActsAs L a⁻¹ α⁻¹ := actsAs_inv L ha
  have h3 : ActsAs L b⁻¹ β⁻¹ := actsAs_inv L hb
  have h12 : ActsAs L ((a * b) * a⁻¹) ((α * β) * α⁻¹) := actsAs_mul L h1 h2
  exact actsAs_mul L h12 h3

private theorem jOn_mem {V : Subgroup G} (hV : V ≤ normalizer (L : Set G))
    {V' : Subgroup (MulAut (L ⧸ center L))} (hV' : jSub L V = V') (x : ↥V) :
    jOn L hV x ∈ V' := by
  rw [← hV', ← range_jOn L hV]
  exact MonoidHom.mem_range.mpr ⟨x, rfl⟩

private theorem mem_Z_of_actsAs (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) {x : G} (hxS : x ∈ s.fr.S) {α : MulAut (L ⧸ center L)}
    (hα : α ∈ s.fr'.Z) (hax : ActsAs L x α) : x ∈ s.fr.Z := by
  rw [← s3_jSub_Z s] at hα
  obtain ⟨w, hwZ, hw⟩ := (mem_jSub L).mp hα
  have hwS : w ∈ s.fr.S := Z_le_S s hwZ
  have : x = w := s3_inj_on_S s hS hZ hxS hwS hax hw
  rw [this]
  exact hwZ

private theorem cen_le_Z (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) {T : Subgroup G} (hTS : T ≤ s.fr.S)
    {T' : Subgroup (MulAut (L ⧸ center L))} (hT' : jSub L T = T')
    (hcen : cen T' ≤ s.fr'.Z) : cen T ≤ s.fr.Z := by
  intro x hx
  simp only [cen, Subgroup.mem_inf] at hx
  obtain ⟨hxT, hxcent⟩ := hx
  have hxS : x ∈ s.fr.S := hTS hxT
  have hax : ActsAs L x (jOn L (s3_S_le_N s) ⟨x, hxS⟩) :=
    jOn_actsAs L (s3_S_le_N s) ⟨x, hxS⟩
  have hαT' : jOn L (s3_S_le_N s) ⟨x, hxS⟩ ∈ T' := by
    rw [← hT']
    exact (mem_jSub L).mpr ⟨x, hxT, hax⟩
  have hαcen : jOn L (s3_S_le_N s) ⟨x, hxS⟩ ∈
      centralizer (T' : Set (MulAut (L ⧸ center L))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro β hβ
    rw [← hT'] at hβ
    obtain ⟨y, hyT, hyβ⟩ := (mem_jSub L).mp hβ
    have hxy : y * x = x * y := (Subgroup.mem_centralizer_iff.mp hxcent) y hyT
    have h1 : ActsAs L (x * y) (jOn L (s3_S_le_N s) ⟨x, hxS⟩ * β) := actsAs_mul L hax hyβ
    have h2 : ActsAs L (x * y) (β * jOn L (s3_S_le_N s) ⟨x, hxS⟩) := by
      rw [← hxy]
      exact actsAs_mul L hyβ hax
    have huniq : jOn L (s3_S_le_N s) ⟨x, hxS⟩ * β =
        β * jOn L (s3_S_le_N s) ⟨x, hxS⟩ := actsAs_unique L h1 h2
    exact huniq.symm
  have hαZ : jOn L (s3_S_le_N s) ⟨x, hxS⟩ ∈ s.fr'.Z :=
    hcen (Subgroup.mem_inf.mpr ⟨hαT', hαcen⟩)
  exact mem_Z_of_actsAs hS hZ s hxS hαZ hax

private theorem Z_le_cen (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) {T : Subgroup G} (hTS : T ≤ s.fr.S) (hzT : s.fr.z ∈ T)
    {T' : Subgroup (MulAut (L ⧸ center L))} (hT' : jSub L T = T')
    (hZ'T' : s.fr'.Z ≤ cen T') : s.fr.Z ≤ cen T := by
  rw [SFrame.Z]
  refine Subgroup.zpowers_le.mpr ?_
  refine Subgroup.mem_inf.mpr ⟨hzT, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hyT
  have hzS : s.fr.z ∈ s.fr.S := hTS hzT
  have hyS : y ∈ s.fr.S := hTS hyT
  have hax : ActsAs L s.fr.z (jOn L (s3_S_le_N s) ⟨s.fr.z, hzS⟩) :=
    jOn_actsAs L (s3_S_le_N s) ⟨s.fr.z, hzS⟩
  have hb : ActsAs L y (jOn L (s3_S_le_N s) ⟨y, hyS⟩) :=
    jOn_actsAs L (s3_S_le_N s) ⟨y, hyS⟩
  have hαZ : jOn L (s3_S_le_N s) ⟨s.fr.z, hzS⟩ ∈ s.fr'.Z := by
    rw [← s3_jSub_Z s]
    exact (mem_jSub L).mpr ⟨s.fr.z, Subgroup.mem_zpowers _, hax⟩
  have hβT' : jOn L (s3_S_le_N s) ⟨y, hyS⟩ ∈ T' := by
    rw [← hT']
    exact (mem_jSub L).mpr ⟨y, hyT, hb⟩
  have hcomm : jOn L (s3_S_le_N s) ⟨s.fr.z, hzS⟩ * jOn L (s3_S_le_N s) ⟨y, hyS⟩ =
      jOn L (s3_S_le_N s) ⟨y, hyS⟩ * jOn L (s3_S_le_N s) ⟨s.fr.z, hzS⟩ :=
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hZ'T' hαZ)).2) _ hβT').symm
  have hconjacts : ActsAs L (s.fr.z * y * s.fr.z⁻¹) (jOn L (s3_S_le_N s) ⟨y, hyS⟩) := by
    have h1 : ActsAs L (s.fr.z * y * s.fr.z⁻¹)
        (jOn L (s3_S_le_N s) ⟨s.fr.z, hzS⟩ * jOn L (s3_S_le_N s) ⟨y, hyS⟩ *
          (jOn L (s3_S_le_N s) ⟨s.fr.z, hzS⟩)⁻¹) := by
      have h12 : ActsAs L (s.fr.z * y)
          (jOn L (s3_S_le_N s) ⟨s.fr.z, hzS⟩ * jOn L (s3_S_le_N s) ⟨y, hyS⟩) :=
        actsAs_mul L hax hb
      exact actsAs_mul L h12 (actsAs_inv L hax)
    have heq : jOn L (s3_S_le_N s) ⟨s.fr.z, hzS⟩ * jOn L (s3_S_le_N s) ⟨y, hyS⟩ *
          (jOn L (s3_S_le_N s) ⟨s.fr.z, hzS⟩)⁻¹ = jOn L (s3_S_le_N s) ⟨y, hyS⟩ := by
      rw [hcomm]
      group
    rw [heq] at h1
    exact h1
  have hzy : s.fr.z * y * s.fr.z⁻¹ = y :=
    s3_inj_on_S s hS hZ (s.fr.S.mul_mem (s.fr.S.mul_mem hzS hyS) (s.fr.S.inv_mem hzS)) hyS
      hconjacts hb
  exact (mul_inv_eq_iff_eq_mul.mp hzy).symm

theorem lfactsA_of_setting (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LFactsA s := by
  obtain ⟨hcardA', hcommA', hsqA', hnonabA', hz'A', hz'ord, hcenA'⟩ :=
    A_facts s.fr' s.facts.2.2.2.1
  have hcenS' : cen s.fr'.S = s.fr'.Z := s.facts.2.2.2.1.1.1
  obtain ⟨hact_a₁, hact_b₁, hact_a₂, hact_b₂, hact_h₀, hact_z⟩ := s3_actsAs_gens s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hinj : Function.Injective (jOn L (s3_A_le_N s)) := by
      intro x y hxy
      exact Subtype.ext (s3_inj_on_S s hS hZ (A_le_S s x.2) (A_le_S s y.2)
        (hxy ▸ jOn_actsAs L (s3_A_le_N s) x) (jOn_actsAs L (s3_A_le_N s) y))
    have hcard : Nat.card ↥s.fr.A = Nat.card ↥(jOn L (s3_A_le_N s)).range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [hcard, range_jOn L (s3_A_le_N s), s3_jSub_A s]
    exact hcardA'
  ·
    intro a ha b hb
    have hax : ActsAs L a (jOn L (s3_A_le_N s) ⟨a, ha⟩) :=
      jOn_actsAs L (s3_A_le_N s) ⟨a, ha⟩
    have hbβ : ActsAs L b (jOn L (s3_A_le_N s) ⟨b, hb⟩) :=
      jOn_actsAs L (s3_A_le_N s) ⟨b, hb⟩
    have hmemZ : ⁅jOn L (s3_A_le_N s) ⟨a, ha⟩, jOn L (s3_A_le_N s) ⟨b, hb⟩⁆ ∈ s.fr'.Z :=
      hcommA' _ (jOn_mem (s3_A_le_N s) (s3_jSub_A s) ⟨a, ha⟩) _
        (jOn_mem (s3_A_le_N s) (s3_jSub_A s) ⟨b, hb⟩)
    exact mem_Z_of_actsAs hS hZ s (A_le_S s (commutator_mem_A s ha hb)) hmemZ
      (actsAs_comm hax hbβ)
  ·
    intro a ha
    have hax : ActsAs L a (jOn L (s3_A_le_N s) ⟨a, ha⟩) :=
      jOn_actsAs L (s3_A_le_N s) ⟨a, ha⟩
    have hmemZ : (jOn L (s3_A_le_N s) ⟨a, ha⟩) ^ 2 ∈ s.fr'.Z :=
      hsqA' _ (jOn_mem (s3_A_le_N s) (s3_jSub_A s) ⟨a, ha⟩)
    exact mem_Z_of_actsAs hS hZ s (A_le_S s (s.fr.A.pow_mem ha 2)) hmemZ (actsAs_pow hax 2)
  ·
    obtain ⟨a', ha'A, b', hb'A, hne⟩ := hnonabA'
    rw [← s3_jSub_A s] at ha'A hb'A
    obtain ⟨a₀, ha₀A, ha₀⟩ := (mem_jSub L).mp ha'A
    obtain ⟨b₀, hb₀A, hb₀⟩ := (mem_jSub L).mp hb'A
    refine ⟨a₀, ha₀A, b₀, hb₀A, ?_⟩
    intro hab
    have h1 : ActsAs L (a₀ * b₀) (a' * b') := actsAs_mul L ha₀ hb₀
    have h2 : ActsAs L (a₀ * b₀) (b' * a') := by
      rw [hab]
      exact actsAs_mul L hb₀ ha₀
    exact hne (actsAs_unique L h1 h2)
  ·
    exact z_mem_A s
  ·
    have hz'2 : s.fr'.z ^ 2 = 1 := by
      rw [← hz'ord]
      exact pow_orderOf_eq_one _
    have haz : ActsAs L (s.fr.z ^ 2) (1 : MulAut (L ⧸ center L)) := by
      rw [← hz'2]
      exact actsAs_pow hact_z 2
    have hz2 : s.fr.z ^ 2 = 1 :=
      s3_inj_on_S s hS hZ (s.fr.S.pow_mem (z_mem_S s) 2) (s.fr.S.one_mem) haz (actsAs_one L)
    refine orderOf_eq_prime hz2 ?_
    intro hz1
    have hz'ne : s.fr'.z ≠ 1 := (orderOf_eq_prime_iff.mp hz'ord).2
    exact hz'ne (by
      have h1 : ActsAs L (1 : G) s.fr'.z := by rw [← hz1]; exact hact_z
      exact actsAs_unique L h1 (actsAs_one L))
  ·
    exact le_antisymm (cen_le_Z hS hZ s (A_le_S s) (s3_jSub_A s) (le_of_eq hcenA'))
      (Z_le_cen hS hZ s (A_le_S s) (z_mem_A s) (s3_jSub_A s) (le_of_eq hcenA'.symm))
  ·
    exact le_antisymm (cen_le_Z hS hZ s le_rfl (s3_jSub_S s) (le_of_eq hcenS'))
      (Z_le_cen hS hZ s le_rfl (z_mem_S s) (s3_jSub_S s) (le_of_eq hcenS'.symm))

end CFSG.OddStandard.HigherRank.YamadaG23
