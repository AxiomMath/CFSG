module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Characters

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem blockOf_subset_irr (m : Ideal BlocksAlgInt) (G : Type*) [Group G]
    (character : G → ℂ) : BlocksBlockOf m G character ⊆ BlocksIrr G := by
  exact fun _ hmember => hmember.1

theorem mem_blockOf_self (m : Ideal BlocksAlgInt) {G : Type*} [Group G]
    {character : G → ℂ} (hcharacter : character ∈ BlocksIrr G) :
    character ∈ BlocksBlockOf m G character := by
  exact ⟨hcharacter, fun _ _ => Iff.rfl⟩

theorem mem_blockOf_symm (m : Ideal BlocksAlgInt) {G : Type*} [Group G]
    {left right : G → ℂ} (hleft : left ∈ BlocksIrr G)
    (hright : right ∈ BlocksBlockOf m G left) : left ∈ BlocksBlockOf m G right := by
  exact ⟨hleft, fun admissible hadmissible => (hright.2 admissible hadmissible).symm⟩

theorem mem_blockOf_trans (m : Ideal BlocksAlgInt) {G : Type*} [Group G]
    {left middle right : G → ℂ} (hmiddle : middle ∈ BlocksBlockOf m G left)
    (hright : right ∈ BlocksBlockOf m G middle) : right ∈ BlocksBlockOf m G left := by
  exact ⟨hright.1, fun admissible hadmissible =>
    (hmiddle.2 admissible hadmissible).trans (hright.2 admissible hadmissible)⟩

theorem blockOf_eq_of_mem (m : Ideal BlocksAlgInt) {G : Type*} [Group G]
    {left right : G → ℂ} (hleft : left ∈ BlocksIrr G)
    (hright : right ∈ BlocksBlockOf m G left) :
    BlocksBlockOf m G right = BlocksBlockOf m G left := by
  apply Set.Subset.antisymm
  · exact fun _ hmember => mem_blockOf_trans m hright hmember
  · exact fun _ hmember => mem_blockOf_trans m (mem_blockOf_symm m hleft hright) hmember

theorem block_nonempty (m : Ideal BlocksAlgInt) {G : Type*} [Group G]
    {block : Set (G → ℂ)} (hblock : BlocksIsBlock m G block) : block.Nonempty := by
  obtain ⟨character, hcharacter, rfl⟩ := hblock
  exact ⟨character, mem_blockOf_self m hcharacter⟩

theorem block_subset_irr (m : Ideal BlocksAlgInt) {G : Type*} [Group G]
    {block : Set (G → ℂ)} (hblock : BlocksIsBlock m G block) : block ⊆ BlocksIrr G := by
  obtain ⟨character, _, rfl⟩ := hblock
  exact blockOf_subset_irr m G character

theorem block_eq_blockOf_member (m : Ideal BlocksAlgInt) {G : Type*} [Group G]
    {block : Set (G → ℂ)} (hblock : BlocksIsBlock m G block) {character : G → ℂ}
    (hcharacter : character ∈ block) : block = BlocksBlockOf m G character := by
  obtain ⟨representative, hrepresentative, rfl⟩ := hblock
  exact (blockOf_eq_of_mem m hrepresentative hcharacter).symm

theorem blocks_eq_of_common_member (m : Ideal BlocksAlgInt) {G : Type*} [Group G]
    {left right : Set (G → ℂ)} (hleft : BlocksIsBlock m G left)
    (hright : BlocksIsBlock m G right) {character : G → ℂ}
    (hcharacterLeft : character ∈ left) (hcharacterRight : character ∈ right) :
    left = right := by
  exact (block_eq_blockOf_member m hleft hcharacterLeft).trans
    (block_eq_blockOf_member m hright hcharacterRight).symm

theorem principal_eq_of_trivial_mem (m : Ideal BlocksAlgInt) {G : Type*} [Group G]
    {block : Set (G → ℂ)} (hblock : BlocksIsBlock m G block)
    (htrivial : (fun _ => (1 : ℂ)) ∈ block) : block = BlocksPrincipalBlock m G := by
  exact block_eq_blockOf_member m hblock htrivial

theorem trivial_mem_principal (m : Ideal BlocksAlgInt) (G : Type*) [Group G] :
    (fun _ => (1 : ℂ)) ∈ BlocksPrincipalBlock m G := by
  exact mem_blockOf_self m (trivial_mem_irr G)

theorem principal_isBlock (m : Ideal BlocksAlgInt) (G : Type*) [Group G] :
    BlocksIsBlock m G (BlocksPrincipalBlock m G) := by
  exact ⟨fun _ => 1, trivial_mem_irr G, rfl⟩

theorem block_principal_iff_trivial_mem (m : Ideal BlocksAlgInt) {G : Type*} [Group G]
    {block : Set (G → ℂ)} (hblock : BlocksIsBlock m G block) :
    block = BlocksPrincipalBlock m G ↔ (fun _ => (1 : ℂ)) ∈ block := by
  constructor
  · rintro rfl
    exact trivial_mem_principal m G
  · exact principal_eq_of_trivial_mem m hblock

end CFSG.BrauerThirdMainTheorem.Helpers
